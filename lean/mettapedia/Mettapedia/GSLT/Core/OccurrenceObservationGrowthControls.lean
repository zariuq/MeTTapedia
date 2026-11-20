import Mettapedia.GSLT.Core.OccurrenceObservationGrowth
import Mathlib.CategoryTheory.Category.Preorder

/-!
# Controls for finite occurrence observations

Growing finite prefixes witness every positive minimum-count observation,
but no fixed initial snapshot supplies every witness. Two equal labels still
give two distinct resources. Collapsing their identities loses a two-take.
An exact count and a bounded greedy choice remain snapshot-sensitive.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.OccurrenceObservationGrowth.Controls

open CategoryTheory
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RegionTakes

def label (_ : Nat) : Unit := ()
def region (_ : Unit) : Bool := true
def worlds (stage : Nat) : Set Nat := (Finset.range stage : Set Nat)

theorem worlds_grow {first second : Nat} (route : first ⟶ second) :
    worlds first ⊆ worlds second :=
  Finset.coe_subset.mpr (Finset.range_subset_range.mpr (leOfHom route))

theorem minimum_at_stage (minimum stage : Nat) :
    PositiveCountRead label (worlds stage) region (minimum ≤ ·) ↔ minimum ≤ stage := by
  have upward : ∀ a b : Nat, a ≤ b → minimum ≤ a → minimum ≤ b :=
    fun _ _ grow accepted => accepted.trans grow
  simpa [worlds, CountRead, regionOf, region] using
    (positiveCountRead_finite_iff (world := Finset.range stage)
      (label := label) (region := region) upward)

theorem minimum_in_union (minimum : Nat) :
    PositiveCountRead label (⋃ stage, worlds stage) region (minimum ≤ ·) := by
  apply (positiveCountRead_union_iff worlds (fun {_ _} => worlds_grow)).2
  exact ⟨minimum, (minimum_at_stage minimum minimum).2 le_rfl⟩

/-- The witness has a real route from the named initial stage and must
reach a prefix containing at least two distinct occurrences. -/
theorem two_resources_require_later_stage :
    ∃ (stage : Nat) (_route : (0 : Nat) ⟶ stage),
      PositiveCountRead label (worlds stage) region (2 ≤ ·) ∧ 2 ≤ stage := by
  obtain ⟨stage, route, read⟩ := positiveCountRead_from_stage worlds
    (fun {_ _} => worlds_grow) 0 (minimum_in_union 2)
  exact ⟨stage, route, read, (minimum_at_stage 2 stage).1 read⟩

theorem no_initial_two_resources :
    ¬ PositiveCountRead label (worlds 0) region (2 ≤ ·) := by
  rw [minimum_at_stage]
  decide

/-- The two selected occurrences carry the same label, but each remains
available to the two-take. Counting a set of labels would lose this fact. -/
theorem same_label_two_take :
    TakesBetween label (Finset.range 2) region 2 (some 2) (Finset.range 2) := by
  refine ⟨?_, by decide, ?_⟩
  · simp [regionOf, region]
  · intro h same
    have : h = 2 := Option.some.inj same.symm
    subst h
    decide

def collapse (_ : Nat) : Nat := 0

theorem collapsed_labels_preserved (occurrence : Nat) :
    label (collapse occurrence) = label occurrence := rfl

theorem collapse_not_faithful :
    ¬ Set.InjOn collapse (Finset.range 2 : Set Nat) := by
  intro faithful
  have same : (0 : Nat) = 1 := faithful (by decide) (by decide) rfl
  exact (by decide : (0 : Nat) ≠ 1) same

theorem collapsed_two_take_refused :
    ¬ TakesBetween label ((Finset.range 2).image collapse) region 2 (some 2)
      ((Finset.range 2).image collapse) := by
  intro takes
  have source : TakesBetween label (Finset.range 2) region
      (Finset.range 2).card (some (Finset.range 2).card) (Finset.range 2) := by
    simpa only [Finset.card_range] using same_label_two_take
  have law := exact_selected_image_iff_faithful
    (targetLabel := label) (targetRegion := region) source collapse
    (fun _ _ => rfl)
  exact collapse_not_faithful (law.1 (by simpa only [Finset.card_range] using takes))

/-- A finite witness for exactly one is insufficient to assert that the
whole store contains exactly one. The upward-closure premise is essential. -/
theorem exact_read_not_positive_extension :
    PositiveCountRead label (worlds 2) region (· = 1) ∧
      ¬ CountRead label (Finset.range 2) region (· = 1) := by
  constructor
  · refine ⟨{0}, ?_, by simp⟩
    intro occurrence member
    have same : occurrence = 0 := Finset.mem_singleton.mp member
    subst occurrence
    exact ⟨by simp [worlds], rfl⟩
  · simp [CountRead, regionOf, region]

theorem bounded_greedy_empty :
    TakesGreedy label ∅ region 0 (some 1) ∅ := by
  refine ⟨⟨by simp [regionOf], by simp, ?_⟩, ?_⟩
  · intro h _
    exact Nat.zero_le h
  · simp [cap, regionOf]

theorem bounded_greedy_choice_changes :
    ¬ TakesGreedy label {0} region 0 (some 1) ∅ := by
  intro greedy
  have most := greedy.most
  simp [cap, regionOf, region] at most

#print axioms two_resources_require_later_stage
#print axioms no_initial_two_resources
#print axioms same_label_two_take
#print axioms collapsed_two_take_refused
#print axioms exact_read_not_positive_extension
#print axioms bounded_greedy_choice_changes

end Mettapedia.GSLT.OccurrenceObservationGrowth.Controls
