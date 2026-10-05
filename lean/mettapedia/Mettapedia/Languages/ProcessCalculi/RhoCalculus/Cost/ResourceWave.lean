import Mettapedia.GSLT.Causality.ResourceWaves
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.PaidResourceSystem

/-!
# Resource selection for located funded rho events

The generic resource selector acts on the existing funded COMM events. Each
entry retains its location, its endpoint occurrences, and its selected purse
heads. Collective availability is exactly the common-source decomposition
required by `CostMatching`, so a selected wave executes through `CostStep`.

The catalogue is supplied explicitly. Its ordering is a scheduling policy;
selection does not establish catalogue completeness, fairness, or exhaustive
search. Deferred occurrences remain available as separate alternatives.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost

open Mettapedia.GSLT.Causality.ResourceInteraction

universe u

namespace CostedEvent

variable {Ground : Type u}

/-- Retain a funded event at its actual location. -/
def resourceEntry (event : CostedEvent Ground) : (costResourceSystem Ground).Entry :=
  ⟨event.location, event, rfl⟩

end CostedEvent

namespace CostResourceWave

variable {Ground : Type u}

/-- Recover the complete event, including the selected purse occurrences. -/
def event (entry : (costResourceSystem Ground).Entry) : CostedEvent Ground :=
  entry.2.val

@[simp] theorem event_resourceEntry (e : CostedEvent Ground) :
    event e.resourceEntry = e := rfl

@[simp] theorem resourceEntry_event (entry : (costResourceSystem Ground).Entry) :
    (event entry).resourceEntry = entry := by
  obtain ⟨location, e, same⟩ := entry
  cases same
  rfl

@[simp] theorem event_location (entry : (costResourceSystem Ground).Entry) :
    (event entry).location = entry.1 := entry.2.property

theorem stepConsume_eq (entries : List (costResourceSystem Ground).Entry) :
    (costResourceSystem Ground).stepConsume entries =
      ((entries.map event).map CostedEvent.consumed).sum := by
  simp only [System.stepConsume, Multiset.map_coe, Multiset.sum_coe, List.map_map]
  exact congrArg List.sum (List.map_congr_left fun entry _ => costResourceSystem_consume entry.2)

theorem stepProduce_eq (entries : List (costResourceSystem Ground).Entry) :
    (costResourceSystem Ground).stepProduce entries =
      ((entries.map event).map CostedEvent.produced).sum := by
  simp only [System.stepProduce, Multiset.map_coe, Multiset.sum_coe, List.map_map]
  exact congrArg List.sum (List.map_congr_left fun entry _ => costResourceSystem_produce entry.2)

theorem stepRead_eq [DecidableEq Ground]
    (entries : List (costResourceSystem Ground).Entry) :
    (costResourceSystem Ground).stepRead entries = 0 := by
  induction entries with
  | nil => rfl
  | cons head tail ih =>
      change ((0 : Multiset (CostTerm Ground)) ::ₘ
        ((tail : Multiset (costResourceSystem Ground).Entry).map fun _ => 0)).sup = 0
      rw [Multiset.sup_cons]
      change 0 ∪ _ = (0 : Multiset (CostTerm Ground))
      rw [Multiset.zero_union]
      exact ih

/-- Joint resource enablement checks both endpoint and purse multiplicities. -/
theorem stepEnables_iff [DecidableEq Ground] (source : CostConfig Ground)
    (entries : List (costResourceSystem Ground).Entry) :
    (costResourceSystem Ground).StepEnables source entries ↔
      ((entries.map event).map CostedEvent.consumed).sum ≤ source := by
  simp only [System.StepEnables, stepConsume_eq, stepRead_eq, add_zero]

/-- Resource enablement is precisely the existing common-source matching
condition. No extra restriction on channel equality is introduced. -/
theorem stepEnables_iff_matching [DecidableEq Ground] (source : CostConfig Ground)
    (entries : List (costResourceSystem Ground).Entry) :
    (costResourceSystem Ground).StepEnables source entries ↔
      ∃ frame, source = costWaveSource (entries.map event) frame := by
  rw [stepEnables_iff, Multiset.le_iff_exists_add]
  rfl

/-- Resource concurrency is exactly rho's endpoint-and-purse compatibility,
including the case where both events have the same channel. -/
theorem concurrent_iff_compatible [DecidableEq Ground] (source : CostConfig Ground)
    (left right : CostedEvent Ground) :
    (costResourceSystem Ground).Concurrent source left.resourceEntry.2
        right.resourceEntry.2 ↔ CostCompatibleAt source left right := by
  unfold System.Concurrent
  rw [costResourceSystem_consume, costResourceSystem_consume, costResourceSystem_read,
    costResourceSystem_read]
  simp only [CostedEvent.resourceEntry, add_zero, and_self, Multiset.le_iff_exists_add,
    CostCompatibleAt, costWaveSource, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]

/-- Any enabled resource event is an ordinary funded step with its original
location and exact debit. -/
theorem enabled_costStep [DecidableEq Ground] (source : CostConfig Ground)
    (entry : (costResourceSystem Ground).Entry)
    (enabled : (costResourceSystem Ground).Enables source entry.2) :
    CostStep source entry.1 (event entry).spend
      ((costResourceSystem Ground).fire source entry.2) := by
  have fits : (event entry).consumed ≤ source := by
    unfold System.Enables at enabled
    rwa [costResourceSystem_consume, costResourceSystem_read, add_zero] at enabled
  have source_eq : (source - (event entry).consumed) + (event entry).consumed =
      source := tsub_add_cancel_of_le fits
  have step := (event entry).toCostStepIn (source - (event entry).consumed)
  rw [source_eq, event_location] at step
  unfold System.fire
  rw [costResourceSystem_consume, costResourceSystem_produce]
  exact step

/-- Scan a finite catalogue using the common resource-wave selector. Both
lists retain full events, not just their labels or endpoint pairs. -/
def select [DecidableEq Ground] (source : CostConfig Ground)
    (candidates : List (CostedEvent Ground)) :
    List (CostedEvent Ground) × List (CostedEvent Ground) :=
  let selected := (costResourceSystem Ground).selectWave source
    (candidates.map CostedEvent.resourceEntry)
  (selected.1.map event, selected.2.map event)

@[simp] theorem map_event_resourceEntry (events : List (CostedEvent Ground)) :
    (events.map CostedEvent.resourceEntry).map event = events := by
  induction events with
  | nil => rfl
  | cons head tail ih =>
      change head :: (tail.map CostedEvent.resourceEntry).map event = head :: tail
      rw [ih]

theorem selected_fits [DecidableEq Ground] (source : CostConfig Ground)
    (candidates : List (CostedEvent Ground)) :
    ((select source candidates).1.map CostedEvent.consumed).sum ≤ source := by
  exact (stepEnables_iff source _).mp
    ((costResourceSystem Ground).selectWave_enabled source _)

theorem selected_sublist [DecidableEq Ground] (source : CostConfig Ground)
    (candidates : List (CostedEvent Ground)) :
    (select source candidates).1.Sublist candidates := by
  have selected := ((costResourceSystem Ground).selectWave_selected_sublist
    source (candidates.map CostedEvent.resourceEntry)).map event
  rw [map_event_resourceEntry] at selected
  exact selected

theorem deferred_sublist [DecidableEq Ground] (source : CostConfig Ground)
    (candidates : List (CostedEvent Ground)) :
    (select source candidates).2.Sublist candidates := by
  have deferred := ((costResourceSystem Ground).selectWave_deferred_sublist
    source (candidates.map CostedEvent.resourceEntry)).map event
  rw [map_event_resourceEntry] at deferred
  exact deferred

/-- Selection partitions occurrences, including repeated equal events. -/
theorem partition [DecidableEq Ground] (source : CostConfig Ground)
    (candidates : List (CostedEvent Ground)) :
    ((select source candidates).1 ++ (select source candidates).2).Perm candidates := by
  have partition := ((costResourceSystem Ground).selectWave_partition source
    (candidates.map CostedEvent.resourceEntry)).map event
  rw [map_event_resourceEntry, List.map_append] at partition
  exact partition

/-- A deferred event cannot be appended to this wave at the same snapshot.
This says nothing about whether a different wave could contain that event. -/
theorem maximal [DecidableEq Ground] (source : CostConfig Ground)
    (candidates : List (CostedEvent Ground)) (e : CostedEvent Ground)
    (deferred : e ∈ (select source candidates).2) :
    ¬ ((e :: (select source candidates).1).map CostedEvent.consumed).sum ≤ source := by
  obtain ⟨entry, member, equal⟩ := List.mem_map.mp deferred
  subst e
  have maximal := (costResourceSystem Ground).selectWave_maximal source
    (candidates.map CostedEvent.resourceEntry) entry member
  intro fits
  apply maximal
  exact (stepEnables_iff source _).mpr fits

/-- An empty selection means that none of the supplied event occurrences is
enabled. It does not assert that the catalogue contains every possible match. -/
theorem empty_iff [DecidableEq Ground] (source : CostConfig Ground)
    (candidates : List (CostedEvent Ground)) :
    (select source candidates).1 = [] ↔
      ∀ e ∈ candidates, ¬ e.consumed ≤ source := by
  change List.map event _ = [] ↔ _
  rw [List.map_eq_nil_iff, (costResourceSystem Ground).selectWave_empty_iff]
  constructor
  · intro noneEnabled e member fits
    apply noneEnabled e.resourceEntry (List.mem_map.mpr ⟨e, member, rfl⟩)
    unfold System.Enables
    rwa [costResourceSystem_consume, costResourceSystem_read, add_zero]
  · intro noneEnabled entry member enabled
    obtain ⟨e, inCandidates, rfl⟩ := List.mem_map.mp member
    apply noneEnabled e inCandidates
    unfold System.Enables at enabled
    rwa [costResourceSystem_consume, costResourceSystem_read, add_zero] at enabled

/-- The selector constructs a matching with the untouched source remainder. -/
def matching [DecidableEq Ground] (source : CostConfig Ground)
    (candidates : List (CostedEvent Ground)) : CostMatching Ground where
  source := source
  events := (select source candidates).1
  frame := source - ((select source candidates).1.map CostedEvent.consumed).sum
  source_eq := (add_tsub_cancel_of_le (selected_fits source candidates)).symm

/-- Every worker ordering of the selected events is a legal ordinary trace. -/
theorem permutation_serializes [DecidableEq Ground] (source : CostConfig Ground)
    (candidates : List (CostedEvent Ground))
    {schedule : List (CostedEvent Ground)}
    (permutation : schedule.Perm (select source candidates).1) :
    CostTrace source (costWaveTrace schedule) (matching source candidates).target :=
  (matching source candidates).permutation_serializes permutation

/-- The receipt retains funding occurrences and is independent of the chosen
serialization. Temporal words are still given by `costWaveTrace schedule`. -/
theorem receipt_eq_of_perm [DecidableEq Ground] (source : CostConfig Ground)
    (candidates : List (CostedEvent Ground))
    {schedule : List (CostedEvent Ground)}
    (permutation : schedule.Perm (select source candidates).1) :
    costWaveReceipt schedule = (matching source candidates).receipt :=
  (matching source candidates).receipt_eq_of_perm permutation

theorem parallelStep [DecidableEq Ground] (source : CostConfig Ground)
    (candidates : List (CostedEvent Ground))
    (nonempty : (select source candidates).1 ≠ []) :
    ParallelCostStep source (matching source candidates).receipt
      (matching source candidates).target :=
  ⟨matching source candidates, rfl, nonempty, rfl, rfl⟩

end CostResourceWave

namespace CostMatching

variable {Ground : Type u} [DecidableEq Ground]

/-- Every previously constructed rho matching satisfies the common resource
contract, including matchings obtained from runtime occurrence indices. -/
theorem resourceEnabled (matching : CostMatching Ground) :
    (costResourceSystem Ground).StepEnables matching.source
      (matching.events.map CostedEvent.resourceEntry) := by
  rw [CostResourceWave.stepEnables_iff_matching,
    CostResourceWave.map_event_resourceEntry]
  exact ⟨matching.frame, matching.source_eq⟩

/-- Both interfaces compute exactly the same residual configuration. -/
theorem resourceTarget (matching : CostMatching Ground) :
    (costResourceSystem Ground).waveTarget matching.source
        (matching.events.map CostedEvent.resourceEntry) = matching.target := by
  rw [System.waveTarget, CostResourceWave.stepConsume_eq,
    CostResourceWave.stepProduce_eq, CostResourceWave.map_event_resourceEntry,
    matching.source_eq]
  simp only [costWaveSource, add_tsub_cancel_left, target, costWaveTarget]
  exact add_comm _ _

end CostMatching

/-- A source containing only one occurrence of a purse term cannot support two
events that both select that occurrence in the same matching. This is the
conflict law of resource systems: two instances that consume a resource present
once are not concurrent. -/
theorem shared_single_purse_conflicts {Ground : Type u}
    [DecidableEq Ground]
    {source : CostConfig Ground} {left right : CostedEvent Ground}
    (purse : CostTerm Ground)
    (source_count : source.count purse = 1)
    (left_uses : purse ∈ left.fundingBefore)
    (right_uses : purse ∈ right.fundingBefore) :
    ¬CostCompatibleAt source left right := fun compatible =>
  (costResourceSystem Ground).not_concurrent_of_shared_consumption source
    left.resourceEntry.2 right.resourceEntry.2 purse
    ((costResourceSystem_consume _).symm ▸ Multiset.mem_add.mpr (Or.inr left_uses))
    ((costResourceSystem_consume _).symm ▸ Multiset.mem_add.mpr (Or.inr right_uses))
    source_count.le ((CostResourceWave.concurrent_iff_compatible source left right).mpr compatible)

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost
