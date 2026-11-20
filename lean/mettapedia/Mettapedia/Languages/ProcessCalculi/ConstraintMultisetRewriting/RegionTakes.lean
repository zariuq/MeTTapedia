import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RegionUpserts
import Mettapedia.Algebra.RuleAlgebra.SingleSpecies

/-!
# Counted takes from a region: a range of counts and a choice of count

A counted take removes some of the occurrences in a region's fiber and does nothing else (`takeOf`). It has two
settings.
- **How many**: a range of counts, at least `lo`, and at most `hi` when `hi = some h` (`hi = none` sets no upper bound).
- **Which count**: either *any* count in the range, each count its own branch (`TakesBetween`), or *greedy*, the largest
  count that both the range and the fiber allow, in one branch (`TakesGreedy`).

Requiring that nothing of the region is left is not a setting of the take. It is a count read on the region: a fixed
count `n` together with a read of `n` takes the whole fiber (`exact_iff_count_read`), and so does a fixed count `n` that
leaves nothing behind (`nothingLeft_iff`).

Familiar takes are settings of the two:
- *take any `n`* is the range `n..n`;
- *take all* is greedy with no bounds, and it takes the whole fiber (`takeAll_iff`, `takeAll_fiber`);
- *take up to `n`* is greedy over `0..n`; take up to 1 is "take one if there is one" (`upToOne_iff`);
- *take all if there are at least `n`* is greedy over `n..`.

The upsert of `RegionUpserts` is take-all followed by a make (`upsert_eq_takeAll_make`).

What each setting does:
- **Refusal.** A range is never refused exactly when `lo = 0` (`takesBetween_never_refused_iff`). A range is admitted
  exactly when the fiber holds `lo` and the range is not empty (`takesBetween_exists_iff`). A greedy take is admitted
  exactly when `lo` is at most the capped fiber size (`takesGreedy_exists_iff`).
- **Monotonicity.** Admission survives a growing world (`takesBetween_mono`, `takesGreedy_exists_mono`), and what a greedy
  take leaves grows with the fiber (`cap_leftover_mono`). This matches Petri nets, which stay well-structured with
  weighted and reset arcs. Requiring that nothing be left, with a finite count, is not monotone: it is admitted in a world
  and refused in a larger one (`Controls.nothing_left_not_monotone`).
- **Makes into the region.** A take of a fixed set commutes with the make of a fresh occurrence
  (`take_commutes_with_fresh_make`), and the set is still a valid choice in the larger world (`takesBetween_mono`).
  A greedy choice does not survive a make into its region (`Controls.greedy_not_kept_by_a_make`).
- **Which reads stay monotone.** A count read (`CountRead`) survives every growth of the world exactly when its allowed
  sizes are closed upward (`countRead_mono_iff`). "Nothing left" allows only one size, so it is not monotone.
- **Sequences.** Two greedy takes from `0` leave the same bag in either order on a region of one label
  (`greedy_sequences_same_bag`): together they take `min (h₁ + h₂) x`. With a positive `lo` the order matters
  (`Controls.greedy_order_matters_when_lo_positive`).
- **Set stores.** In a set store a region of one label holds at most one occurrence (`set_store_fiber_card_le_one`), so a
  fixed count of two or more on it is always refused (`set_store_fixed_refused`). On a region of several labels a
  counted take still means something (`Controls.set_store_patterns_take_two`).
- **Greedy selects among the branches.** Greedy choices are exactly the choices in the range of the largest size
  (`greedy_iff_largest`). Making that selection needs the fiber's exact size.
- **Independence.** Two takes of fixed sets give the same world in either order (`takes_commute`). Both orders are
  possible exactly when the sets are disjoint (`both_orders_iff_disjoint`).
- **Branching.** On a region of one label, two choices leave the same multiset of labels exactly when they have the
  same size (`same_bag_of_card_eq`, `same_bag_iff_card_eq`): up to the bag laws, the branches of a take are its
  admitted counts.
  - A fixed count leaves one bag (`fixed_same_bag`), and so does a greedy take (`takesGreedy_same_bag`). A matcher may
    follow one choice instead of all `C(x, n)` of them.
  - A range leaves one bag per count (`Controls.range_branches_by_count`).
  - On a region of several labels, which occurrences are taken shows (`Controls.choice_shows_on_a_wide_region`).
- **Counting.** Number the occurrences by `ℕ`.
  - A fixed count `n` is a firing of the single-species rule `⟨n, 0, 0, false⟩` that keeps nothing
    (`fixed_iff_firingsOn`). It has `C(x, n)` choices, the rule's match count (`mem_fixed_choices`,
    `fixed_count_eq_matchesCount`).
  - Leaving nothing is the rule's `exhaust` flag (`nothingLeft_iff_firingsOn`).
  - Greedy up to `h` is, in each world, a firing of one of `h + 1` rules (`greedy_some_iff_firingsOn`,
    `greedy_some_finitely_many_rules`).
  - Greedy with no upper bound needs the rule `⟨x, 0, 0, true⟩` for the fiber's size `x` (`greedy_none_iff_firingsOn`),
    and no finite set of rules takes every fiber whole (`takeAll_not_finitely_many_rules`). Take-all is a family of
    rules, not a finite set of them.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RegionTakes

open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RegionUpserts (upsert)
open Mettapedia.Algebra.RuleAlgebra

universe uO uT

variable {O : Type uO} {T : Type uT}

/-- The commit that takes the occurrences `chosen` and does nothing else. -/
def takeOf (chosen : Finset O) : Commit O T :=
  ⟨chosen, ∅, ∅, []⟩

/-- The commit that makes the occurrence `made` and does nothing else. -/
def makeOf (made : O) : Commit O T :=
  ⟨∅, ∅, {made}, []⟩

/-- **A counted take with a range**: `chosen` lies in the region's fiber in `world`, and its size is at least `lo` and
at most `h` when `hi = some h`. -/
structure TakesBetween (label : O → T) (world : Finset O) (region : T → Bool) (lo : ℕ) (hi : Option ℕ)
    (chosen : Finset O) : Prop where
  within : chosen ⊆ regionOf label world region
  atLeast : lo ≤ chosen.card
  atMost : ∀ h, hi = some h → chosen.card ≤ h

/-- The largest count that a bound `hi` allows on a fiber of `x` occurrences. -/
def cap : Option ℕ → ℕ → ℕ
  | none, x => x
  | some h, x => min h x

/-- **A greedy counted take** takes as many occurrences as the range and the fiber allow. -/
structure TakesGreedy (label : O → T) (world : Finset O) (region : T → Bool) (lo : ℕ) (hi : Option ℕ)
    (chosen : Finset O) : Prop where
  takes : TakesBetween label world region lo hi chosen
  most : chosen.card = cap hi (regionOf label world region).card

/-- **take-all**: every occurrence of the region's fiber in `world`. -/
def takeAll (label : O → T) (world : Finset O) (region : T → Bool) : Commit O T :=
  takeOf (regionOf label world region)

/-! ## Taking a set of occurrences -/

theorem cap_le (hi : Option ℕ) (x : ℕ) : cap hi x ≤ x := by
  cases hi with
  | none => exact le_rfl
  | some h => exact min_le_right h x

theorem cap_fits (hi : Option ℕ) (x : ℕ) : ∀ h, hi = some h → cap hi x ≤ h := by
  intro h eq
  subst eq
  exact min_le_left h x

theorem cap_mono (hi : Option ℕ) {x x' : ℕ} (le : x ≤ x') : cap hi x ≤ cap hi x' := by
  cases hi with
  | none => exact le
  | some h => exact min_le_min_left h le

/-- **What a greedy take leaves grows with the fiber.** -/
theorem cap_leftover_mono (hi : Option ℕ) {x x' : ℕ} (le : x ≤ x') : x - cap hi x ≤ x' - cap hi x' := by
  cases hi with
  | none => simp [cap]
  | some h =>
    show x - min h x ≤ x' - min h x'
    omega

theorem fire_takeOf [DecidableEq O] (world chosen : Finset O) :
    fire world (takeOf (T := T) chosen) = world \ chosen := by
  simp only [fire, takeOf, Finset.union_empty]

theorem regionOf_sdiff [DecidableEq O] (label : O → T) (world chosen : Finset O) (region : T → Bool) :
    regionOf label (world \ chosen) region = regionOf label world region \ chosen := by
  ext o
  simp only [regionOf, Finset.mem_filter, Finset.mem_sdiff]
  tauto

theorem regionOf_mono {label : O → T} {world world' : Finset O} {region : T → Bool} (grow : world ⊆ world') :
    regionOf label world region ⊆ regionOf label world' region :=
  Finset.filter_subset_filter _ grow

/-- **Nothing outside the region changes** when the taken occurrences lie in the region's fiber. -/
theorem takeOf_outside [DecidableEq O] {label : O → T} {world : Finset O} {region : T → Bool}
    {chosen : Finset O} (within : chosen ⊆ regionOf label world region) {o : O}
    (outside : region (label o) = false) :
    o ∈ fire world (takeOf (T := T) chosen) ↔ o ∈ world := by
  rw [fire_takeOf, Finset.mem_sdiff]
  constructor
  · exact fun member => member.1
  · intro inWorld
    refine ⟨inWorld, fun taken => ?_⟩
    have held := within taken
    simp only [regionOf, Finset.mem_filter, outside] at held
    exact Bool.false_ne_true held.2

/-- **A take leaves the fiber smaller by what it took.** -/
theorem takesBetween_fiber_card [DecidableEq O] {label : O → T} {world : Finset O} {region : T → Bool}
    {lo : ℕ} {hi : Option ℕ} {chosen : Finset O} (takes : TakesBetween label world region lo hi chosen) :
    (regionOf label (fire world (takeOf (T := T) chosen)) region).card =
      (regionOf label world region).card - chosen.card := by
  rw [fire_takeOf, regionOf_sdiff, Finset.card_sdiff_of_subset takes.within]

/-! ## Refusal -/

/-- **A range is admitted exactly when the fiber holds `lo` and the range is not empty.** -/
theorem takesBetween_exists_iff {label : O → T} {world : Finset O} {region : T → Bool} {lo : ℕ}
    {hi : Option ℕ} :
    (∃ chosen, TakesBetween label world region lo hi chosen) ↔
      lo ≤ (regionOf label world region).card ∧ ∀ h, hi = some h → lo ≤ h := by
  constructor
  · rintro ⟨chosen, takes⟩
    exact ⟨takes.atLeast.trans (Finset.card_le_card takes.within),
      fun h eq => takes.atLeast.trans (takes.atMost h eq)⟩
  · rintro ⟨enough, range⟩
    obtain ⟨chosen, within, card⟩ := Finset.exists_subset_card_eq enough
    refine ⟨chosen, within, card.ge, fun h eq => ?_⟩
    rw [card]
    exact range h eq

/-- **A range is never refused exactly when it starts at zero.** -/
theorem takesBetween_never_refused_iff {label : O → T} {region : T → Bool} {lo : ℕ} {hi : Option ℕ} :
    (∀ world, ∃ chosen, TakesBetween label world region lo hi chosen) ↔ lo = 0 := by
  constructor
  · intro always
    obtain ⟨chosen, takes⟩ := always ∅
    have within := takes.within
    have atLeast := takes.atLeast
    have empty : regionOf label (∅ : Finset O) region = ∅ := by simp [regionOf]
    rw [empty, Finset.subset_empty] at within
    rw [within, Finset.card_empty] at atLeast
    omega
  · rintro rfl world
    refine ⟨∅, Finset.empty_subset _, Nat.zero_le _, fun h _ => ?_⟩
    rw [Finset.card_empty]
    exact Nat.zero_le h

/-- **A greedy take is admitted exactly when `lo` is at most the capped fiber size.** -/
theorem takesGreedy_exists_iff {label : O → T} {world : Finset O} {region : T → Bool} {lo : ℕ}
    {hi : Option ℕ} :
    (∃ chosen, TakesGreedy label world region lo hi chosen) ↔
      lo ≤ cap hi (regionOf label world region).card := by
  constructor
  · rintro ⟨chosen, takes, most⟩
    rw [← most]
    exact takes.atLeast
  · intro enough
    obtain ⟨chosen, within, card⟩ :=
      Finset.exists_subset_card_eq (cap_le hi (regionOf label world region).card)
    refine ⟨chosen, ⟨within, ?_, fun h eq => ?_⟩, card⟩
    · rw [card]
      exact enough
    · rw [card]
      exact cap_fits hi _ h eq

/-! ## Monotonicity -/

/-- **A choice stays valid when the world grows.** -/
theorem takesBetween_mono {label : O → T} {world world' : Finset O} {region : T → Bool} {lo : ℕ}
    {hi : Option ℕ} {chosen : Finset O} (grow : world ⊆ world')
    (takes : TakesBetween label world region lo hi chosen) :
    TakesBetween label world' region lo hi chosen :=
  ⟨takes.within.trans (regionOf_mono grow), takes.atLeast, takes.atMost⟩

/-- **A greedy take stays admitted when the world grows.** -/
theorem takesGreedy_exists_mono {label : O → T} {world world' : Finset O} {region : T → Bool} {lo : ℕ}
    {hi : Option ℕ} (grow : world ⊆ world')
    (admitted : ∃ chosen, TakesGreedy label world region lo hi chosen) :
    ∃ chosen, TakesGreedy label world' region lo hi chosen := by
  rw [takesGreedy_exists_iff] at admitted ⊢
  exact admitted.trans (cap_mono hi (Finset.card_le_card (regionOf_mono grow)))

/-! ## Makes into the region -/

/-- **A take of a fixed set commutes with the make of a fresh occurrence.** -/
theorem take_commutes_with_fresh_make [DecidableEq O] {world chosen : Finset O} {made : O}
    (fresh : made ∉ chosen) :
    fire (fire world (takeOf (T := T) chosen)) (makeOf (T := T) made) =
      fire (fire world (makeOf (T := T) made)) (takeOf (T := T) chosen) := by
  ext o
  simp only [mem_fire, takeOf, makeOf, Finset.notMem_empty, not_false_eq_true, and_true, or_false,
    Finset.mem_singleton]
  constructor
  · rintro (⟨inWorld, notChosen⟩ | rfl)
    · exact ⟨Or.inl inWorld, notChosen⟩
    · exact ⟨Or.inr rfl, fresh⟩
  · rintro ⟨inWorld | rfl, notChosen⟩
    · exact Or.inl ⟨inWorld, notChosen⟩
    · exact Or.inr rfl

/-! ## Branching -/

/-- **On a region of one label, two choices of the same size leave the same bag.** -/
theorem same_bag_of_card_eq [DecidableEq O] {label : O → T} {world : Finset O} {region : T → Bool} {t : T}
    (single : ∀ o ∈ regionOf label world region, label o = t) {chosen₁ chosen₂ : Finset O}
    (within₁ : chosen₁ ⊆ regionOf label world region) (within₂ : chosen₂ ⊆ regionOf label world region)
    (same : chosen₁.card = chosen₂.card) :
    (fire world (takeOf (T := T) chosen₁)).val.map label =
      (fire world (takeOf (T := T) chosen₂)).val.map label := by
  have bag : ∀ chosen, chosen ⊆ regionOf label world region →
      (fire world (takeOf (T := T) chosen)).val.map label + Multiset.replicate chosen.card t =
        world.val.map label := by
    intro chosen within
    have whole : (world.val - chosen.val) + chosen.val = world.val :=
      tsub_add_cancel_of_le (Finset.val_le_iff.mpr (within.trans (Finset.filter_subset _ _)))
    have labels : chosen.val.map label = Multiset.replicate chosen.card t := by
      rw [Multiset.eq_replicate]
      refine ⟨Multiset.card_map _ _, ?_⟩
      intro b member
      obtain ⟨o, inChosen, rfl⟩ := Multiset.mem_map.mp member
      exact single o (within inChosen)
    calc (fire world (takeOf (T := T) chosen)).val.map label + Multiset.replicate chosen.card t
        = (world.val - chosen.val).map label + chosen.val.map label := by
          rw [fire_takeOf, Finset.sdiff_val, labels]
      _ = ((world.val - chosen.val) + chosen.val).map label := (Multiset.map_add _ _ _).symm
      _ = world.val.map label := by rw [whole]
  have one := bag chosen₁ within₁
  have two := bag chosen₂ within₂
  rw [same] at one
  exact add_right_cancel (one.trans two.symm)

/-- **On a region of one label, a fixed count leaves one bag.** -/
theorem fixed_same_bag [DecidableEq O] {label : O → T} {world : Finset O} {region : T → Bool} {t : T}
    (single : ∀ o ∈ regionOf label world region, label o = t) {n : ℕ} {chosen₁ chosen₂ : Finset O}
    (takes₁ : TakesBetween label world region n (some n) chosen₁)
    (takes₂ : TakesBetween label world region n (some n) chosen₂) :
    (fire world (takeOf (T := T) chosen₁)).val.map label =
      (fire world (takeOf (T := T) chosen₂)).val.map label :=
  same_bag_of_card_eq single takes₁.within takes₂.within
    ((le_antisymm (takes₁.atMost n rfl) takes₁.atLeast).trans
      (le_antisymm (takes₂.atMost n rfl) takes₂.atLeast).symm)

/-- **On a region of one label, a greedy take leaves one bag.** -/
theorem takesGreedy_same_bag [DecidableEq O] {label : O → T} {world : Finset O} {region : T → Bool} {t : T}
    (single : ∀ o ∈ regionOf label world region, label o = t) {lo : ℕ} {hi : Option ℕ}
    {chosen₁ chosen₂ : Finset O} (greedy₁ : TakesGreedy label world region lo hi chosen₁)
    (greedy₂ : TakesGreedy label world region lo hi chosen₂) :
    (fire world (takeOf (T := T) chosen₁)).val.map label =
      (fire world (takeOf (T := T) chosen₂)).val.map label :=
  same_bag_of_card_eq single greedy₁.takes.within greedy₂.takes.within (greedy₁.most.trans greedy₂.most.symm)

/-! ## Familiar settings -/

/-- **take-all is greedy with no bounds**: it takes the whole fiber. -/
theorem takeAll_iff {label : O → T} {world : Finset O} {region : T → Bool} {chosen : Finset O} :
    TakesGreedy label world region 0 none chosen ↔ chosen = regionOf label world region := by
  constructor
  · intro greedy
    exact Finset.eq_of_subset_of_card_le greedy.takes.within (le_of_eq greedy.most.symm)
  · rintro rfl
    exact ⟨⟨Finset.Subset.refl _, Nat.zero_le _, fun h eq => by cases eq⟩, rfl⟩

/-- **Take-all empties the fiber.** -/
theorem takeAll_fiber [DecidableEq O] (label : O → T) (world : Finset O) (region : T → Bool) :
    regionOf label (fire world (takeAll label world region)) region = ∅ := by
  rw [takeAll, fire_takeOf, regionOf_sdiff, Finset.sdiff_self]

/-- **An upsert is take-all followed by a make.** -/
theorem upsert_eq_takeAll_make (label : O → T) (world : Finset O) (region : T → Bool) (made : O) :
    upsert label world region made = { takeAll label world region with made := {made} } :=
  rfl

/-- **Take up to 1 is "take one if there is one"**: on an empty fiber it takes nothing, and otherwise it takes one
occurrence of the fiber. -/
theorem upToOne_iff {label : O → T} {world : Finset O} {region : T → Bool} {chosen : Finset O} :
    TakesGreedy label world region 0 (some 1) chosen ↔
      (regionOf label world region = ∅ ∧ chosen = ∅) ∨ ∃ o ∈ regionOf label world region, chosen = {o} := by
  constructor
  · intro greedy
    have within := greedy.takes.within
    have most : chosen.card = min 1 (regionOf label world region).card := greedy.most
    by_cases empty : regionOf label world region = ∅
    · rw [empty] at within
      exact Or.inl ⟨empty, Finset.subset_empty.mp within⟩
    · have pos : 0 < (regionOf label world region).card :=
        Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr empty)
      have one : chosen.card = 1 := by omega
      obtain ⟨o, rfl⟩ := Finset.card_eq_one.mp one
      exact Or.inr ⟨o, within (Finset.mem_singleton_self o), rfl⟩
  · rintro (⟨empty, rfl⟩ | ⟨o, member, rfl⟩)
    · refine ⟨⟨Finset.empty_subset _, Nat.zero_le _, fun h _ => ?_⟩, ?_⟩
      · rw [Finset.card_empty]
        exact Nat.zero_le h
      · simp [cap, empty]
    · have pos : 0 < (regionOf label world region).card := Finset.card_pos.mpr ⟨o, member⟩
      refine ⟨⟨Finset.singleton_subset_iff.mpr member, Nat.zero_le _, fun h eq => ?_⟩, ?_⟩
      · cases eq
        exact (Finset.card_singleton o).le
      · show ({o} : Finset O).card = min 1 (regionOf label world region).card
        rw [Finset.card_singleton]
        omega

/-! ## Leaving nothing is a count read -/

/-- **A fixed count `n` with a read of `n` takes the whole fiber.** -/
theorem exact_iff_count_read {label : O → T} {world : Finset O} {region : T → Bool} {n : ℕ}
    {chosen : Finset O} :
    (TakesBetween label world region n (some n) chosen ∧ (regionOf label world region).card = n) ↔
      (regionOf label world region).card = n ∧ chosen = regionOf label world region := by
  constructor
  · rintro ⟨takes, count⟩
    have ge := takes.atLeast
    refine ⟨count, Finset.eq_of_subset_of_card_le takes.within ?_⟩
    omega
  · rintro ⟨count, rfl⟩
    exact ⟨⟨Finset.Subset.refl _, count.ge, fun h eq => by cases eq; exact count.le⟩, count⟩

/-- **A fixed count `n` that leaves nothing of the region takes the whole fiber, which holds `n`.** -/
theorem nothingLeft_iff [DecidableEq O] {label : O → T} {world : Finset O} {region : T → Bool} {n : ℕ}
    {chosen : Finset O} :
    (TakesBetween label world region n (some n) chosen ∧
        regionOf label (fire world (takeOf (T := T) chosen)) region = ∅) ↔
      (regionOf label world region).card = n ∧ chosen = regionOf label world region := by
  constructor
  · rintro ⟨takes, noneLeft⟩
    rw [fire_takeOf, regionOf_sdiff, Finset.sdiff_eq_empty_iff_subset] at noneLeft
    have same : chosen = regionOf label world region := Finset.Subset.antisymm takes.within noneLeft
    have ge := takes.atLeast
    have le := takes.atMost n rfl
    refine ⟨?_, same⟩
    rw [← same]
    omega
  · rintro ⟨count, rfl⟩
    refine ⟨⟨Finset.Subset.refl _, count.ge, fun h eq => by cases eq; exact count.le⟩, ?_⟩
    rw [fire_takeOf, regionOf_sdiff, Finset.sdiff_self]

/-! ## The rule algebra's counting -/

/-- **The choices of a fixed count `n` are the `n`-element subsets of the fiber.** -/
theorem mem_fixed_choices {label : O → T} {world : Finset O} {region : T → Bool} {n : ℕ} {chosen : Finset O} :
    chosen ∈ (regionOf label world region).powersetCard n ↔ TakesBetween label world region n (some n) chosen := by
  rw [Finset.mem_powersetCard]
  constructor
  · rintro ⟨within, card⟩
    exact ⟨within, card.ge, fun h eq => by cases eq; exact card.le⟩
  · intro takes
    exact ⟨takes.within, le_antisymm (takes.atMost n rfl) takes.atLeast⟩

/-- **A fixed count `n` is a firing of the single-species rule `⟨n, 0, 0, false⟩` that keeps nothing.** -/
theorem fixed_iff_firingsOn {label : ℕ → T} {world : Finset ℕ} {region : T → Bool} {n : ℕ}
    {chosen : Finset ℕ} :
    TakesBetween label world region n (some n) chosen ↔
      (chosen, ∅) ∈ firingsOn ⟨n, 0, 0, false⟩ (regionOf label world region) := by
  rw [mem_firingsOn]
  constructor
  · intro takes
    have ge := takes.atLeast
    have le := takes.atMost n rfl
    exact ⟨takes.within, (by show chosen.card = n; omega), Finset.empty_subset _, Finset.card_empty,
      by simp⟩
  · rintro ⟨within, card, -, -, -⟩
    have card' : chosen.card = n := card
    exact ⟨within, card'.ge, fun h eq => by cases eq; exact card'.le⟩

/-- **Leaving nothing is the rule's `exhaust` flag**: a fixed count `n` that leaves nothing is a firing of
`⟨n, 0, 0, true⟩` that keeps nothing. -/
theorem nothingLeft_iff_firingsOn {label : ℕ → T} {world : Finset ℕ} {region : T → Bool} {n : ℕ}
    {chosen : Finset ℕ} :
    (TakesBetween label world region n (some n) chosen ∧
        regionOf label (fire world (takeOf (T := T) chosen)) region = ∅) ↔
      (chosen, ∅) ∈ firingsOn ⟨n, 0, 0, true⟩ (regionOf label world region) := by
  rw [nothingLeft_iff, mem_firingsOn]
  constructor
  · rintro ⟨card, rfl⟩
    exact ⟨Finset.Subset.refl _, card, Finset.empty_subset _, Finset.card_empty,
      fun _ => Finset.union_empty _⟩
  · rintro ⟨_, card, -, -, all⟩
    have same : chosen = regionOf label world region := by simpa using all rfl
    refine ⟨?_, same⟩
    rw [← same]
    exact card

/-- **A fixed count `n` has as many choices as the rule `⟨n, 0, 0, false⟩` has matches.** -/
theorem fixed_count_eq_matchesCount (label : ℕ → T) (world : Finset ℕ) (region : T → Bool) (n : ℕ) :
    ((regionOf label world region).powersetCard n).card =
      SingleRule.matchesCount ⟨n, 0, 0, false⟩ (regionOf label world region).card := by
  rw [Finset.card_powersetCard]
  simp [SingleRule.matchesCount]

/-! ## Greedy is the largest choice in the range -/

theorem TakesBetween.card_le_cap {label : O → T} {world : Finset O} {region : T → Bool} {lo : ℕ}
    {hi : Option ℕ} {chosen : Finset O} (takes : TakesBetween label world region lo hi chosen) :
    chosen.card ≤ cap hi (regionOf label world region).card := by
  cases hi with
  | none => exact Finset.card_le_card takes.within
  | some h => exact le_min (takes.atMost h rfl) (Finset.card_le_card takes.within)

/-- **Greedy choices are the choices of the largest size in the range.** -/
theorem greedy_iff_largest {label : O → T} {world : Finset O} {region : T → Bool} {lo : ℕ} {hi : Option ℕ}
    {chosen : Finset O} :
    TakesGreedy label world region lo hi chosen ↔
      TakesBetween label world region lo hi chosen ∧
        ∀ other, TakesBetween label world region lo hi other → other.card ≤ chosen.card := by
  constructor
  · intro greedy
    refine ⟨greedy.takes, fun other takes => ?_⟩
    rw [greedy.most]
    exact takes.card_le_cap
  · rintro ⟨takes, largest⟩
    refine ⟨takes, le_antisymm takes.card_le_cap ?_⟩
    obtain ⟨other, within, card⟩ :=
      Finset.exists_subset_card_eq (cap_le hi (regionOf label world region).card)
    have otherTakes : TakesBetween label world region lo hi other := by
      refine ⟨within, ?_, fun h eq => ?_⟩
      · rw [card]
        exact takes.atLeast.trans takes.card_le_cap
      · rw [card]
        exact cap_fits hi _ h eq
    rw [← card]
    exact largest other otherTakes

/-! ## Independence of takes -/

/-- **Two takes of fixed sets give the same world in either order.** -/
theorem takes_commute [DecidableEq O] (world A B : Finset O) :
    fire (fire world (takeOf (T := T) A)) (takeOf (T := T) B) =
      fire (fire world (takeOf (T := T) B)) (takeOf (T := T) A) := by
  rw [fire_takeOf, fire_takeOf, fire_takeOf, fire_takeOf, sdiff_sdiff_comm]

/-- **Two takes of fixed sets can run in either order exactly when the sets are disjoint**: each must still find its
occurrences after the other has fired. -/
theorem both_orders_iff_disjoint [DecidableEq O] {label : O → T} {world : Finset O} {region : T → Bool}
    {A B : Finset O} (withinA : A ⊆ regionOf label world region) (withinB : B ⊆ regionOf label world region) :
    (B ⊆ regionOf label (fire world (takeOf (T := T) A)) region ∧
        A ⊆ regionOf label (fire world (takeOf (T := T) B)) region) ↔ Disjoint A B := by
  rw [fire_takeOf, fire_takeOf, regionOf_sdiff, regionOf_sdiff]
  constructor
  · rintro ⟨afterA, -⟩
    rw [Finset.disjoint_left]
    intro o inA inB
    exact (Finset.mem_sdiff.mp (afterA inB)).2 inA
  · intro disjoint
    exact ⟨fun o inB => Finset.mem_sdiff.mpr ⟨withinB inB, fun inA => Finset.disjoint_left.mp disjoint inA inB⟩,
      fun o inA => Finset.mem_sdiff.mpr ⟨withinA inA, Finset.disjoint_left.mp disjoint inA⟩⟩

/-! ## The branches of a take are its counts -/

/-- **On a region of one label, two choices leave the same bag exactly when they have the same size.** Up to the bag
laws, the branches of a counted take are its admitted counts. -/
theorem same_bag_iff_card_eq [DecidableEq O] {label : O → T} {world : Finset O} {region : T → Bool} {t : T}
    (single : ∀ o ∈ regionOf label world region, label o = t) {chosen₁ chosen₂ : Finset O}
    (within₁ : chosen₁ ⊆ regionOf label world region) (within₂ : chosen₂ ⊆ regionOf label world region) :
    (fire world (takeOf (T := T) chosen₁)).val.map label =
        (fire world (takeOf (T := T) chosen₂)).val.map label ↔
      chosen₁.card = chosen₂.card := by
  refine ⟨fun same => ?_, same_bag_of_card_eq single within₁ within₂⟩
  have sizes := congrArg Multiset.card same
  rw [Multiset.card_map, Multiset.card_map, fire_takeOf, fire_takeOf] at sizes
  have sub₁ : chosen₁ ⊆ world := within₁.trans (Finset.filter_subset _ _)
  have sub₂ : chosen₂ ⊆ world := within₂.trans (Finset.filter_subset _ _)
  have c₁ := Finset.card_sdiff_of_subset sub₁
  have c₂ := Finset.card_sdiff_of_subset sub₂
  have l₁ := Finset.card_le_card sub₁
  have l₂ := Finset.card_le_card sub₂
  change (world \ chosen₁).card = (world \ chosen₂).card at sizes
  omega

/-! ## Bounded and unbounded greedy in the rule algebra -/

/-- **Greedy up to `h` is, in each world, one of `h + 1` rules**: `⟨h, 0, 0, false⟩` when the fiber holds at least `h`,
and `⟨x, 0, 0, true⟩`, taking the whole fiber of `x`, when it holds fewer. -/
theorem greedy_some_iff_firingsOn {label : ℕ → T} {world : Finset ℕ} {region : T → Bool} {lo h : ℕ}
    {chosen : Finset ℕ} :
    TakesGreedy label world region lo (some h) chosen ↔
      (lo ≤ h ∧ h ≤ (regionOf label world region).card ∧
          (chosen, ∅) ∈ firingsOn ⟨h, 0, 0, false⟩ (regionOf label world region)) ∨
        (lo ≤ (regionOf label world region).card ∧ (regionOf label world region).card < h ∧
          (chosen, ∅) ∈ firingsOn ⟨(regionOf label world region).card, 0, 0, true⟩
            (regionOf label world region)) := by
  rw [mem_firingsOn, mem_firingsOn]
  constructor
  · intro greedy
    have within := greedy.takes.within
    have atLeast := greedy.takes.atLeast
    have most : chosen.card = min h (regionOf label world region).card := greedy.most
    by_cases enough : h ≤ (regionOf label world region).card
    · have card : chosen.card = h := by rw [most, min_eq_left enough]
      exact Or.inl ⟨by omega, enough, within, card, Finset.empty_subset _, Finset.card_empty, by simp⟩
    · have fewer : (regionOf label world region).card < h := Nat.lt_of_not_le enough
      have card : chosen.card = (regionOf label world region).card := by rw [most, min_eq_right fewer.le]
      have whole : chosen = regionOf label world region := Finset.eq_of_subset_of_card_le within card.ge
      exact Or.inr ⟨by omega, fewer, within, card, Finset.empty_subset _, Finset.card_empty,
        fun _ => by simp [whole]⟩
  · rintro (⟨lo_le, enough, within, card, -, -, -⟩ | ⟨lo_le, fewer, within, card, -, -, -⟩)
    · have card' : chosen.card = h := card
      exact ⟨⟨within, by omega, fun h' eq => by cases eq; omega⟩,
        by show chosen.card = min h (regionOf label world region).card; rw [card', min_eq_left enough]⟩
    · have card' : chosen.card = (regionOf label world region).card := card
      exact ⟨⟨within, by omega, fun h' eq => by cases eq; omega⟩,
        by show chosen.card = min h (regionOf label world region).card; rw [card', min_eq_right fewer.le]⟩

/-- **Greedy with no upper bound takes the whole fiber, through the rule indexed by the fiber's size.** -/
theorem greedy_none_iff_firingsOn {label : ℕ → T} {world : Finset ℕ} {region : T → Bool} {lo : ℕ}
    {chosen : Finset ℕ} :
    TakesGreedy label world region lo none chosen ↔
      lo ≤ (regionOf label world region).card ∧
        (chosen, ∅) ∈ firingsOn ⟨(regionOf label world region).card, 0, 0, true⟩ (regionOf label world region) := by
  rw [mem_firingsOn]
  constructor
  · intro greedy
    have within := greedy.takes.within
    have atLeast := greedy.takes.atLeast
    have card : chosen.card = (regionOf label world region).card := greedy.most
    have whole : chosen = regionOf label world region := Finset.eq_of_subset_of_card_le within card.ge
    exact ⟨by omega, within, card, Finset.empty_subset _, Finset.card_empty, fun _ => by simp [whole]⟩
  · rintro ⟨lo_le, within, card, -, -, -⟩
    have card' : chosen.card = (regionOf label world region).card := card
    exact ⟨⟨within, by omega, fun h eq => by cases eq⟩, card'⟩

/-- The `h + 1` rules that greedy up to `h` uses. -/
def boundedGreedyRules (h : ℕ) : Finset SingleRule :=
  insert ⟨h, 0, 0, false⟩ ((Finset.range h).image fun k => ⟨k, 0, 0, true⟩)

/-- **Greedy up to `h` needs only finitely many rules**: in every world, a greedy choice is a firing of one of the
`h + 1` rules `boundedGreedyRules h`. -/
theorem greedy_some_finitely_many_rules {label : ℕ → T} {world : Finset ℕ} {region : T → Bool} {lo h : ℕ}
    {chosen : Finset ℕ} (greedy : TakesGreedy label world region lo (some h) chosen) :
    ∃ r ∈ boundedGreedyRules h, (chosen, ∅) ∈ firingsOn r (regionOf label world region) := by
  rcases greedy_some_iff_firingsOn.mp greedy with ⟨-, -, firing⟩ | ⟨-, fewer, firing⟩
  · exact ⟨_, Finset.mem_insert_self _ _, firing⟩
  · exact ⟨_, Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨_, Finset.mem_range.mpr fewer, rfl⟩), firing⟩

/-- **No finite set of rules takes every fiber whole**: for any finite set of single-species rules there is a fiber
size at which none of them has a firing that takes the whole fiber. So greedy with no upper bound (take-all) is a family
of rules indexed by the fiber's size, not a finite set of rules. -/
theorem takeAll_not_finitely_many_rules (rules : Finset SingleRule) :
    ∃ x : ℕ, ∀ r ∈ rules, ∀ p ∈ firingsOn r (Finset.range x), p.1 ≠ Finset.range x := by
  refine ⟨rules.sup SingleRule.take + 1, fun r member p firing whole => ?_⟩
  rw [mem_firingsOn] at firing
  obtain ⟨-, card, -⟩ := firing
  have le : r.take ≤ rules.sup SingleRule.take := Finset.le_sup member
  rw [whole, Finset.card_range] at card
  omega

/-! ## Count reads and monotonicity -/

/-- **A count read**: the size of the region's fiber lies in `allowed`. -/
def CountRead (label : O → T) (world : Finset O) (region : T → Bool) (allowed : ℕ → Prop) : Prop :=
  allowed (regionOf label world region).card

/-- **A count read survives every growth of the world exactly when its allowed sizes are closed upward.** Stated on
`ℕ`-numbered occurrences of one label, where every size is reached. -/
theorem countRead_mono_iff (allowed : ℕ → Prop) :
    (∀ world world' : Finset ℕ, world ⊆ world' →
        CountRead (fun _ : ℕ => ()) world (fun _ => true) allowed →
        CountRead (fun _ : ℕ => ()) world' (fun _ => true) allowed) ↔
      ∀ x y, x ≤ y → allowed x → allowed y := by
  constructor
  · intro mono x y le read
    have grown := mono (Finset.range x) (Finset.range y) (Finset.range_subset_range.mpr le)
    simp only [CountRead, regionOf, Finset.filter_true, Finset.card_range] at grown
    exact grown read
  · intro up world world' grow read
    exact up _ _ (Finset.card_le_card (regionOf_mono grow)) read

/-! ## Two greedy takes in sequence -/

theorem cap_sequence_comm (hi₁ hi₂ : Option ℕ) (x : ℕ) :
    cap hi₁ x + cap hi₂ (x - cap hi₁ x) = cap hi₂ x + cap hi₁ (x - cap hi₂ x) := by
  cases hi₁ <;> cases hi₂ <;> simp only [cap] <;> omega

theorem fire_takeOf_twice [DecidableEq O] (world A B : Finset O) :
    fire (fire world (takeOf (T := T) A)) (takeOf (T := T) B) = fire world (takeOf (T := T) (A ∪ B)) := by
  ext o
  rw [fire_takeOf, fire_takeOf, fire_takeOf]
  simp only [Finset.mem_sdiff, Finset.mem_union]
  tauto

/-- **Two greedy takes from `0` leave the same bag in either order** on a region of one label: whichever runs first, the
two together take `min (h₁ + h₂) x` occurrences (with no bound read as unbounded). -/
theorem greedy_sequences_same_bag [DecidableEq O] {label : O → T} {world : Finset O} {region : T → Bool} {t : T}
    (single : ∀ o ∈ regionOf label world region, label o = t) {hi₁ hi₂ : Option ℕ}
    {a₁ a₂ b₂ b₁ : Finset O}
    (a₁greedy : TakesGreedy label world region 0 hi₁ a₁)
    (a₂greedy : TakesGreedy label (fire world (takeOf (T := T) a₁)) region 0 hi₂ a₂)
    (b₂greedy : TakesGreedy label world region 0 hi₂ b₂)
    (b₁greedy : TakesGreedy label (fire world (takeOf (T := T) b₂)) region 0 hi₁ b₁) :
    (fire (fire world (takeOf (T := T) a₁)) (takeOf (T := T) a₂)).val.map label =
      (fire (fire world (takeOf (T := T) b₂)) (takeOf (T := T) b₁)).val.map label := by
  have total : ∀ {hiA hiB : Option ℕ} {A B : Finset O},
      TakesGreedy label world region 0 hiA A →
      TakesGreedy label (fire world (takeOf (T := T) A)) region 0 hiB B →
      (A ∪ B) ⊆ regionOf label world region ∧
        (A ∪ B).card = cap hiA (regionOf label world region).card +
          cap hiB ((regionOf label world region).card - cap hiA (regionOf label world region).card) := by
    intro hiA hiB A B first second
    have withinB := second.takes.within
    rw [fire_takeOf, regionOf_sdiff] at withinB
    have disjoint : Disjoint A B :=
      Finset.disjoint_left.mpr fun _ inA inB => (Finset.mem_sdiff.mp (withinB inB)).2 inA
    refine ⟨Finset.union_subset first.takes.within fun _ inB => (Finset.mem_sdiff.mp (withinB inB)).1, ?_⟩
    rw [Finset.card_union_of_disjoint disjoint, first.most, second.most, takesBetween_fiber_card first.takes,
      first.most]
  obtain ⟨withinA, cardA⟩ := total a₁greedy a₂greedy
  obtain ⟨withinB, cardB⟩ := total b₂greedy b₁greedy
  rw [fire_takeOf_twice, fire_takeOf_twice]
  exact same_bag_of_card_eq single withinA withinB (by rw [cardA, cardB, cap_sequence_comm])

/-! ## Set stores -/

/-- **In a set store a region of one label holds at most one occurrence.** -/
theorem set_store_fiber_card_le_one {label : O → T} {world : Finset O} {region : T → Bool} {t : T}
    (setStore : Set.InjOn label world) (single : ∀ o ∈ regionOf label world region, label o = t) :
    (regionOf label world region).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro a inA b inB
  apply setStore (Finset.filter_subset _ _ inA) (Finset.filter_subset _ _ inB)
  rw [single a inA, single b inB]

/-- **In a set store a fixed count of two or more on a region of one label is always refused.** -/
theorem set_store_fixed_refused {label : O → T} {world : Finset O} {region : T → Bool} {t : T}
    (setStore : Set.InjOn label world) (single : ∀ o ∈ regionOf label world region, label o = t)
    {n : ℕ} (two : 2 ≤ n) : ¬ ∃ chosen, TakesBetween label world region n (some n) chosen := by
  rw [takesBetween_exists_iff]
  rintro ⟨enough, -⟩
  have atMostOne := set_store_fiber_card_le_one setStore single
  omega

namespace Controls

/-- **On a region of two labels the choice shows**: taking `0` or taking `1` from `{0, 1}` are both a fixed count 1, and
they leave different bags. -/
theorem choice_shows_on_a_wide_region :
    TakesBetween (id : ℕ → ℕ) {0, 1} (fun _ => true) 1 (some 1) {0} ∧
      TakesBetween (id : ℕ → ℕ) {0, 1} (fun _ => true) 1 (some 1) {1} ∧
      (fire ({0, 1} : Finset ℕ) (takeOf (T := ℕ) {0})).val.map id ≠
        (fire ({0, 1} : Finset ℕ) (takeOf (T := ℕ) {1})).val.map id := by
  refine ⟨mem_fixed_choices.mp (by decide), mem_fixed_choices.mp (by decide), by decide⟩

/-- **A range leaves one bag per count**: on a region of one label, taking nothing and taking one occurrence are both in
the range `0..1`, and they leave different bags. -/
theorem range_branches_by_count :
    TakesBetween (fun _ : ℕ => (0 : ℕ)) {0, 1} (fun _ => true) 0 (some 1) ∅ ∧
      TakesBetween (fun _ : ℕ => (0 : ℕ)) {0, 1} (fun _ => true) 0 (some 1) {0} ∧
      (fire ({0, 1} : Finset ℕ) (takeOf (T := ℕ) ∅)).val.map (fun _ : ℕ => (0 : ℕ)) ≠
        (fire ({0, 1} : Finset ℕ) (takeOf (T := ℕ) {0})).val.map (fun _ : ℕ => (0 : ℕ)) := by
  refine ⟨⟨Finset.empty_subset _, Nat.zero_le _, fun h eq => ?_⟩,
    ⟨by decide, Nat.zero_le _, fun h eq => ?_⟩, by decide⟩
  · cases eq
    decide
  · cases eq
    decide

/-- **A greedy choice does not survive a make into its region**: in `{0}` the greedy take up to 2 takes `{0}`; after a
make of `1` the same choice is no longer greedy. -/
theorem greedy_not_kept_by_a_make :
    TakesGreedy (id : ℕ → ℕ) {0} (fun _ => true) 0 (some 2) {0} ∧
      ¬ TakesGreedy (id : ℕ → ℕ) (fire {0} (makeOf (T := ℕ) 1)) (fun _ => true) 0 (some 2) {0} := by
  refine ⟨⟨⟨by decide, Nat.zero_le _, fun h eq => ?_⟩, by decide⟩, fun greedy => ?_⟩
  · cases eq
    decide
  · exact absurd greedy.most (by decide)

/-- **Requiring that nothing be left is not monotone.** The fixed count 1 that leaves nothing is admitted in `{0}` and
refused in `{0, 1}`. Decided in `{0}` and fired after a make of `1`, it leaves `{1}`. -/
theorem nothing_left_not_monotone :
    (TakesBetween (id : ℕ → ℕ) {0} (fun _ => true) 1 (some 1) {0} ∧
        regionOf (id : ℕ → ℕ) (fire {0} (takeOf (T := ℕ) {0})) (fun _ => true) = ∅) ∧
      (∀ chosen, ¬ (TakesBetween (id : ℕ → ℕ) {0, 1} (fun _ => true) 1 (some 1) chosen ∧
        regionOf (id : ℕ → ℕ) (fire {0, 1} (takeOf (T := ℕ) chosen)) (fun _ => true) = ∅)) ∧
      regionOf (id : ℕ → ℕ) (fire (fire {0} (makeOf (T := ℕ) 1)) (takeOf (T := ℕ) {0})) (fun _ => true) =
        {1} := by
  refine ⟨nothingLeft_iff.mpr ⟨by decide, by decide⟩, fun chosen held => ?_, by decide⟩
  exact absurd (nothingLeft_iff.mp held).1 (by decide)

/-- **With a positive `lo`, the order of two greedy takes matters.** On three occurrences of one label, greedy from 2 with
no bound takes all three, after which greedy 1..1 is refused. In the other order greedy 1..1 takes one occurrence and
greedy from 2 takes the remaining two. -/
theorem greedy_order_matters_when_lo_positive :
    TakesGreedy (fun _ : ℕ => (0 : ℕ)) {0, 1, 2} (fun _ => true) 2 none {0, 1, 2} ∧
      ¬ (∃ chosen, TakesGreedy (fun _ : ℕ => (0 : ℕ)) (fire {0, 1, 2} (takeOf (T := ℕ) {0, 1, 2}))
          (fun _ => true) 1 (some 1) chosen) ∧
      TakesGreedy (fun _ : ℕ => (0 : ℕ)) {0, 1, 2} (fun _ => true) 1 (some 1) {0} ∧
      TakesGreedy (fun _ : ℕ => (0 : ℕ)) (fire {0, 1, 2} (takeOf (T := ℕ) {0})) (fun _ => true) 2 none {1, 2} := by
  refine ⟨⟨⟨by decide, by decide, fun h eq => by cases eq⟩, by decide⟩, ?_,
    ⟨⟨by decide, by decide, fun h eq => by cases eq; decide⟩, by decide⟩,
    ⟨⟨by decide, by decide, fun h eq => by cases eq⟩, by decide⟩⟩
  rw [takesGreedy_exists_iff]
  decide

/-- **Over a set store a counted take still means something on a region of several labels**: two distinct labels, two
occurrences, a fixed count 2. -/
theorem set_store_patterns_take_two :
    Set.InjOn (id : ℕ → ℕ) (({0, 1} : Finset ℕ) : Set ℕ) ∧
      TakesBetween (id : ℕ → ℕ) {0, 1} (fun _ => true) 2 (some 2) {0, 1} :=
  ⟨Set.injOn_id _, mem_fixed_choices.mp (by decide)⟩

end Controls

#print axioms countRead_mono_iff
#print axioms cap_sequence_comm
#print axioms fire_takeOf_twice
#print axioms greedy_sequences_same_bag
#print axioms set_store_fiber_card_le_one
#print axioms set_store_fixed_refused
#print axioms Controls.greedy_order_matters_when_lo_positive
#print axioms Controls.set_store_patterns_take_two
#print axioms cap_leftover_mono
#print axioms takeOf_outside
#print axioms takesBetween_fiber_card
#print axioms takesBetween_exists_iff
#print axioms takesBetween_never_refused_iff
#print axioms takesGreedy_exists_iff
#print axioms takesBetween_mono
#print axioms takesGreedy_exists_mono
#print axioms take_commutes_with_fresh_make
#print axioms same_bag_of_card_eq
#print axioms fixed_same_bag
#print axioms takesGreedy_same_bag
#print axioms takeAll_iff
#print axioms takeAll_fiber
#print axioms upsert_eq_takeAll_make
#print axioms upToOne_iff
#print axioms exact_iff_count_read
#print axioms nothingLeft_iff
#print axioms mem_fixed_choices
#print axioms fixed_iff_firingsOn
#print axioms nothingLeft_iff_firingsOn
#print axioms fixed_count_eq_matchesCount
#print axioms greedy_iff_largest
#print axioms takes_commute
#print axioms both_orders_iff_disjoint
#print axioms same_bag_iff_card_eq
#print axioms greedy_some_iff_firingsOn
#print axioms greedy_none_iff_firingsOn
#print axioms greedy_some_finitely_many_rules
#print axioms takeAll_not_finitely_many_rules
#print axioms Controls.choice_shows_on_a_wide_region
#print axioms Controls.range_branches_by_count
#print axioms Controls.greedy_not_kept_by_a_make
#print axioms Controls.nothing_left_not_monotone

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RegionTakes
