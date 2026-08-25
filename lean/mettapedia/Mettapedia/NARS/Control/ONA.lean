import Mathlib.Data.Finset.Card
import Mathlib.Tactic
import Mettapedia.Evidence.SourceScope
import Mettapedia.NARS.TruthFunctions

/-!
# OpenNARS for Applications control contracts

Patrick Hammer and Tony Lofthouse, *OpenNARS for Applications: Architecture
and Control* (AGI 2020), distinguish two resource operations:

* relative forgetting changes the ranking used for attention;
* absolute forgetting evicts items so finite memories remain within capacity.

They rank concepts by a raw usefulness
`useCount / (recency + 1)` and normalize it by `u / (u + 1)`. Their cycling
event queue and concept memory are bounded, and their operating cycle selects
fixed numbers of events and concepts. The constant-cycle claim is consequently
relative to fixed configuration sizes and bounded primitive operations; this
module records those premises rather than treating asymptotic cost as a
property of the logical truth functions.

The definitions below formalize the reusable control contracts. They do not
identify NAL with ONA: NAL supplies inference and truth functions, whereas ONA
is one resource-bounded architecture executing them.
-/

namespace Mettapedia.NARS.Control.ONA

open Mettapedia.NARS.TruthFunctions

universe uTerm uSource uItem

/-! ## Source-retaining events -/

/-- The control-relevant fields of an ONA event. The evidential stamp is the
finite source scope used to prevent statistically dependent premises from being
combined as independent evidence. -/
structure Event (Term : Type uTerm) (Source : Type uSource) where
  term : Term
  truth : TV
  stamp : Finset Source
  occurrenceTime : ℕ
  priority : ℝ
  priority_nonneg : 0 ≤ priority
  priority_le_one : priority ≤ 1

namespace Event

variable {Term : Type uTerm} {Source : Type uSource}

/-- The shared source-scope criterion used before treating two event bodies as
statistically independent. -/
def Independent [DecidableEq Source]
    (left right : Event Term Source) : Prop :=
  Mettapedia.Evidence.SourceScope.Independent left.stamp right.stamp

end Event

/-! ## Usefulness -/

/-- The two historical quantities from which ONA computes concept usefulness. -/
structure UsageRecord where
  lastUsed : ℕ
  useCount : ℕ

namespace UsageRecord

/-- Time since last use, with natural-number truncation if a malformed clock
value precedes `lastUsed`. Normal operation supplies monotone clock values. -/
def recency (now : ℕ) (record : UsageRecord) : ℕ :=
  now - record.lastUsed

/-- Hammer--Lofthouse raw usefulness: repeated use raises the numerator while
recency lowers the score. -/
noncomputable def rawUsefulness (now : ℕ) (record : UsageRecord) : ℝ :=
  (record.useCount : ℝ) / ((record.recency now : ℝ) + 1)

/-- Normalize a nonnegative raw score into `[0,1)`. -/
noncomputable def normalize (raw : ℝ) : ℝ :=
  raw / (raw + 1)

/-- ONA concept usefulness. -/
noncomputable def usefulness (now : ℕ) (record : UsageRecord) : ℝ :=
  normalize (record.rawUsefulness now)

theorem rawUsefulness_nonneg (now : ℕ) (record : UsageRecord) :
    0 ≤ record.rawUsefulness now := by
  unfold rawUsefulness
  positivity

theorem rawUsefulness_denominator_pos (now : ℕ) (record : UsageRecord) :
    0 < (record.recency now : ℝ) + 1 := by
  positivity

theorem normalize_mono {left right : ℝ}
    (left_nonneg : 0 ≤ left) (left_le_right : left ≤ right) :
    normalize left ≤ normalize right := by
  have left_denom_pos : 0 < left + 1 := by linarith
  have right_nonneg : 0 ≤ right := left_nonneg.trans left_le_right
  have right_denom_pos : 0 < right + 1 := by linarith
  rw [normalize, normalize, div_le_div_iff₀ left_denom_pos right_denom_pos]
  nlinarith

theorem normalize_nonneg {raw : ℝ} (raw_nonneg : 0 ≤ raw) :
    0 ≤ normalize raw := by
  unfold normalize
  positivity

theorem normalize_lt_one {raw : ℝ} (raw_nonneg : 0 ≤ raw) :
    normalize raw < 1 := by
  unfold normalize
  exact (div_lt_one (by linarith)).2 (by linarith)

theorem usefulness_mem_Ico (now : ℕ) (record : UsageRecord) :
    record.usefulness now ∈ Set.Ico (0 : ℝ) 1 := by
  exact ⟨normalize_nonneg (rawUsefulness_nonneg now record),
    normalize_lt_one (rawUsefulness_nonneg now record)⟩

/-- With recency fixed, increasing use count cannot lower usefulness. -/
theorem usefulness_mono_useCount
    (recency : ℕ) {leftCount rightCount : ℕ}
    (count_le : leftCount ≤ rightCount) :
    normalize ((leftCount : ℝ) / ((recency : ℝ) + 1)) ≤
      normalize ((rightCount : ℝ) / ((recency : ℝ) + 1)) := by
  apply normalize_mono
  · positivity
  · exact div_le_div_of_nonneg_right (by exact_mod_cast count_le) (by positivity)

/-- With use count fixed, greater recency cannot raise raw usefulness. -/
theorem rawUsefulness_antitone_recency
    (useCount : ℕ) {recent old : ℕ} (recency_le : recent ≤ old) :
    (useCount : ℝ) / ((old : ℝ) + 1) ≤
      (useCount : ℝ) / ((recent : ℝ) + 1) := by
  apply div_le_div_of_nonneg_left
  · positivity
  · positivity
  · have cast_le : (recent : ℝ) ≤ (old : ℝ) := by
      exact_mod_cast recency_le
    linarith

theorem zero_useCount_usefulness (now lastUsed : ℕ) :
    (UsageRecord.mk lastUsed 0).usefulness now = 0 := by
  simp [usefulness, rawUsefulness, normalize]

/-- Positive canary: one use at recency zero has normalized usefulness `1/2`. -/
theorem one_fresh_usefulness :
    (UsageRecord.mk 0 1).usefulness 0 = 1 / 2 := by
  norm_num [usefulness, rawUsefulness, recency, normalize]

/-- Negative canary: the same single use is less useful after one idle cycle. -/
theorem one_old_usefulness_lt_fresh :
    (UsageRecord.mk 0 1).usefulness 1 <
      (UsageRecord.mk 0 1).usefulness 0 := by
  norm_num [usefulness, rawUsefulness, recency, normalize]

end UsageRecord

/-! ## Bounded absolute forgetting -/

/-- A finite store whose capacity invariant is carried by the state. -/
structure BoundedStore (Item : Type uItem) where
  capacity : ℕ
  items : Finset Item
  card_le_capacity : items.card ≤ capacity

namespace BoundedStore

variable {Item : Type uItem} [DecidableEq Item]

/-- Absolute forgetting removes an item and preserves the memory bound. -/
def evict (store : BoundedStore Item) (item : Item) : BoundedStore Item where
  capacity := store.capacity
  items := store.items.erase item
  card_le_capacity := by
    calc
      (store.items.erase item).card ≤ store.items.card := Finset.card_erase_le
      _ ≤ store.capacity := store.card_le_capacity

@[simp] theorem evict_capacity (store : BoundedStore Item) (item : Item) :
    (store.evict item).capacity = store.capacity := rfl

@[simp] theorem evict_items (store : BoundedStore Item) (item : Item) :
    (store.evict item).items = store.items.erase item := rfl

theorem evict_card_le_capacity (store : BoundedStore Item) (item : Item) :
    (store.evict item).items.card ≤ store.capacity :=
  (store.evict item).card_le_capacity

/-- Result of bounded insertion, retaining the proof that no unrelated item
was introduced while making room for the candidate. -/
structure InsertResult (before : BoundedStore Item) (item : Item) where
  after : BoundedStore Item
  retained_from_insert : after.items ⊆ insert item before.items

/-- Insert a candidate and retain a capacity-bounded subset. This is the common
contract behind an implementation that evicts its least-ranked item; ranking
correctness is stated separately so the capacity theorem does not assume a
particular tie-breaking algorithm. -/
def insertWithEviction
    (store : BoundedStore Item) (item : Item) (retained : Finset Item)
    (retained_from_insert : retained ⊆ insert item store.items)
    (retained_bounded : retained.card ≤ store.capacity) :
    InsertResult store item where
  after := {
    capacity := store.capacity
    items := retained
    card_le_capacity := retained_bounded
  }
  retained_from_insert := retained_from_insert

theorem insertWithEviction_subset
    (store : BoundedStore Item) (item : Item) (retained : Finset Item)
    (retained_from_insert : retained ⊆ insert item store.items)
    (retained_bounded : retained.card ≤ store.capacity) :
    (store.insertWithEviction item retained retained_from_insert retained_bounded).after.items ⊆
      insert item store.items :=
  (store.insertWithEviction item retained retained_from_insert retained_bounded).retained_from_insert

end BoundedStore

/-! ## Attention and ranking stability -/

section Attention

variable {Item : Type uItem} [DecidableEq Item]

/-- Items meeting the current attention threshold. -/
noncomputable def attentionFocus (score : Item → ℝ) (threshold : ℝ)
    (items : Finset Item) : Finset Item :=
  items.filter fun item => threshold ≤ score item

omit [DecidableEq Item] in
theorem mem_attentionFocus_iff
    (score : Item → ℝ) (threshold : ℝ) (items : Finset Item) (item : Item) :
    item ∈ attentionFocus score threshold items ↔
      item ∈ items ∧ threshold ≤ score item := by
  simp [attentionFocus]

/-- Evicting an item below threshold leaves the attentional focus unchanged. -/
theorem attentionFocus_erase_of_below_threshold
    (score : Item → ℝ) (threshold : ℝ) (items : Finset Item) (item : Item)
    (below : score item < threshold) :
    attentionFocus score threshold (items.erase item) =
      attentionFocus score threshold items := by
  ext candidate
  simp only [attentionFocus, Finset.mem_filter, Finset.mem_erase]
  constructor
  · rintro ⟨⟨different, present⟩, selected⟩
    exact ⟨present, selected⟩
  · rintro ⟨present, selected⟩
    refine ⟨⟨?_, present⟩, selected⟩
    intro same
    subst candidate
    exact (not_le_of_gt below) selected

/-- Removing an attended singleton does change the focus: attention stability
is conditional on evicting below-threshold material, not a general erasure law. -/
theorem attentionFocus_erase_attended_singleton_changes :
    attentionFocus (fun _ : Fin 1 => (1 : ℝ)) (1 / 2)
        (({0} : Finset (Fin 1)).erase 0) ≠
      attentionFocus (fun _ : Fin 1 => (1 : ℝ)) (1 / 2)
        ({0} : Finset (Fin 1)) := by
  norm_num [attentionFocus]

end Attention

/-! ## Explicit cycle-cost premises -/

/-- Fixed selection counts in one ONA configuration. -/
structure CycleConfiguration where
  eventSelections : ℕ
  conceptSelections : ℕ
  inferencePatterns : ℕ

/-- Upper bounds for the primitive operations used by a configured cycle. -/
structure PrimitiveCostBound where
  selectEvent : ℕ
  selectConcept : ℕ
  testEvidenceOverlap : ℕ
  testInferencePattern : ℕ
  publishResult : ℕ

/-- A transparent upper bound for one configured operating cycle. -/
def cycleWork (configuration : CycleConfiguration)
    (cost : PrimitiveCostBound) : ℕ :=
  configuration.eventSelections * cost.selectEvent +
    configuration.eventSelections * configuration.conceptSelections *
      (cost.selectConcept + cost.testEvidenceOverlap +
        configuration.inferencePatterns * cost.testInferencePattern +
        cost.publishResult)

/-- With configuration and primitive bounds fixed, the cycle-work bound is
independent of the current memory cardinality. -/
theorem cycleWork_memory_independent
    (configuration : CycleConfiguration) (cost : PrimitiveCostBound)
    (_leftMemorySize _rightMemorySize : ℕ) :
    cycleWork configuration cost = cycleWork configuration cost := by
  rfl

/-- A full memory scan is the negative control: it has no uniform bound over
all memory sizes. -/
def fullScanWork (memorySize : ℕ) : ℕ := memorySize

theorem fullScanWork_not_uniformly_bounded :
    ¬ ∃ bound : ℕ, ∀ memorySize : ℕ, fullScanWork memorySize ≤ bound := by
  rintro ⟨bound, bounded⟩
  have impossible := bounded (bound + 1)
  simp [fullScanWork] at impossible

#print axioms UsageRecord.usefulness_mem_Ico
#print axioms BoundedStore.evict_card_le_capacity
#print axioms attentionFocus_erase_of_below_threshold
#print axioms fullScanWork_not_uniformly_bounded

end Mettapedia.NARS.Control.ONA
