import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RegionTakes
import Mathlib.CategoryTheory.Filtered.Basic

/-!
# Finite positive occurrence observations under growth

Distinct resource occurrences are independent of their labels. A counted
take transports when its selected occurrences remain distinct; labels may
coincide. No injectivity away from that finite selection is required.

An upward-closed count read has a positive extension to an arbitrary store:
it is witnessed by a finite selection of occurrences. This extension agrees
with the existing finite-store read and commutes with filtered unions whose
maps retain occurrence identities. A named original stage has an explicit
route to a witnessing stage. Exact counts, exhaustive selections and absence
are snapshot observations and are not asserted to have this extension.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.OccurrenceObservationGrowth

open CategoryTheory
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RegionTakes

universe uO uP uT uU uJ vJ

variable {O : Type uO} {P : Type uP} {T : Type uT} {U : Type uU}

/-- Transport a take using only faithfulness on its selected occurrences.
The target may identify other occurrences; labels need not be distinct. -/
theorem takesBetween_image [DecidableEq P]
    {label : O → T} {targetLabel : P → U} {world chosen : Finset O}
    {region : T → Bool} {targetRegion : U → Bool} {lo : Nat} {hi : Option Nat}
    (takes : TakesBetween label world region lo hi chosen) (map : O → P)
    (faithful : Set.InjOn map (chosen : Set O))
    (regions : ∀ occurrence ∈ chosen,
      targetRegion (targetLabel (map occurrence)) = region (label occurrence)) :
    TakesBetween targetLabel (world.image map) targetRegion lo hi (chosen.image map) := by
  have count : (chosen.image map).card = chosen.card := Finset.card_image_of_injOn faithful
  refine ⟨?_, count ▸ takes.atLeast, fun h eq => count ▸ takes.atMost h eq⟩
  intro target member
  obtain ⟨occurrence, selected, rfl⟩ := Finset.mem_image.mp member
  have within := takes.within selected
  simp only [regionOf, Finset.mem_filter] at within ⊢
  refine ⟨Finset.mem_image.mpr ⟨occurrence, within.1, rfl⟩, ?_⟩
  simpa only [regions occurrence selected] using within.2

/-- For the exact selected count, faithfulness on the selection is also
necessary. Labels and their interpretation may change through the supplied
region square; the resource cardinality is a separate obligation. -/
theorem exact_selected_image_iff_faithful [DecidableEq P]
    {label : O → T} {targetLabel : P → U} {world chosen : Finset O}
    {region : T → Bool} {targetRegion : U → Bool}
    (takes : TakesBetween label world region chosen.card (some chosen.card) chosen)
    (map : O → P) (regions : ∀ occurrence ∈ chosen,
      targetRegion (targetLabel (map occurrence)) = region (label occurrence)) :
    TakesBetween targetLabel (world.image map) targetRegion chosen.card
      (some chosen.card) (chosen.image map) ↔ Set.InjOn map (chosen : Set O) := by
  constructor
  · intro image
    exact Finset.card_image_iff.mp (le_antisymm Finset.card_image_le image.atLeast)
  · intro faithful
    exact takesBetween_image takes map faithful regions

/-- The finite-support faithfulness condition composes on exactly the
selected image, without requiring globally injective maps. -/
theorem faithful_on_selection_comp [DecidableEq P]
    {Q : Type*} {chosen : Finset O} {first : O → P} {second : P → Q}
    (left : Set.InjOn first (chosen : Set O))
    (right : Set.InjOn second (chosen.image first : Set P)) :
    Set.InjOn (second ∘ first) (chosen : Set O) := by
  intro a ha b hb same
  exact left ha hb (right (Finset.mem_image.mpr ⟨a, ha, rfl⟩)
    (Finset.mem_image.mpr ⟨b, hb, rfl⟩) same)

/-- A positive count observation carries its finite occurrence witness.
For a non-upward-closed predicate this is a different observation from an
exact read of the complete store. -/
def PositiveCountRead (label : O → T) (world : Set O)
    (region : T → Bool) (allowed : Nat → Prop) : Prop :=
  ∃ chosen : Finset O,
    (∀ occurrence ∈ chosen, occurrence ∈ world ∧ region (label occurrence) = true) ∧
      allowed chosen.card

theorem positiveCountRead_mono {label : O → T} {world world' : Set O}
    {region : T → Bool} {allowed : Nat → Prop}
    (grow : world ⊆ world') (read : PositiveCountRead label world region allowed) :
    PositiveCountRead label world' region allowed := by
  obtain ⟨chosen, within, count⟩ := read
  exact ⟨chosen, fun occurrence member =>
    ⟨grow (within occurrence member).1, (within occurrence member).2⟩, count⟩

/-- For the upward-closed reads characterized by `countRead_mono_iff`,
finite witnesses agree exactly with the existing complete finite-store read. -/
theorem positiveCountRead_finite_iff {label : O → T} {world : Finset O}
    {region : T → Bool} {allowed : Nat → Prop}
    (upward : ∀ a b, a ≤ b → allowed a → allowed b) :
    PositiveCountRead label (world : Set O) region allowed ↔ CountRead label world region allowed := by
  constructor
  · rintro ⟨chosen, within, count⟩
    apply upward chosen.card _ ?_ count
    apply Finset.card_le_card
    intro occurrence member
    exact Finset.mem_filter.mpr (within occurrence member)
  · intro read
    refine ⟨regionOf label world region, ?_, read⟩
    intro occurrence member
    exact Finset.mem_filter.mp member

section FilteredGrowth

variable {J : Type uJ} [Category.{vJ} J] [IsFiltered J]
variable (world : J → Set O)
variable (grows : ∀ {first second : J}, (first ⟶ second) → world first ⊆ world second)

include grows

/-- Finitely many identified occurrences in the union already coexist at
one stage. Order-independent membership does not collapse their identities. -/
theorem finite_occurrences_at_stage [DecidableEq O] (chosen : Finset O)
    (present : ∀ occurrence ∈ chosen, ∃ stage, occurrence ∈ world stage) :
    ∃ stage, ∀ occurrence ∈ chosen, occurrence ∈ world stage := by
  induction chosen using Finset.induction_on with
  | empty =>
      obtain ⟨stage⟩ := (IsFiltered.nonempty : Nonempty J)
      exact ⟨stage, by simp⟩
  | @insert occurrence rest fresh induction =>
      obtain ⟨first, member⟩ := present occurrence (Finset.mem_insert_self occurrence rest)
      obtain ⟨second, members⟩ := induction (fun item inside =>
        present item (Finset.mem_insert_of_mem inside))
      refine ⟨IsFiltered.max first second, ?_⟩
      intro item inside
      rcases Finset.mem_insert.mp inside with same | old
      · subst item
        exact grows (IsFiltered.leftToMax first second) member
      · exact grows (IsFiltered.rightToMax first second) (members item old)

/-- Positive reads commute with filtered unions. This is a finite-witness
law, not a claim that a complete answer bag or a negative read has ended. -/
theorem positiveCountRead_union_iff [DecidableEq O]
    {label : O → T} {region : T → Bool} {allowed : Nat → Prop} :
    PositiveCountRead label (⋃ stage, world stage) region allowed ↔
      ∃ stage, PositiveCountRead label (world stage) region allowed := by
  constructor
  · rintro ⟨chosen, within, count⟩
    obtain ⟨stage, members⟩ := finite_occurrences_at_stage world grows chosen
      (fun occurrence member => Set.mem_iUnion.mp (within occurrence member).1)
    exact ⟨stage, chosen, fun occurrence member =>
      ⟨members occurrence member, (within occurrence member).2⟩, count⟩
  · rintro ⟨stage, read⟩
    exact positiveCountRead_mono (Set.subset_iUnion world stage) read

/-- A retained original stage has an actual forward route to the stage
witnessing a positive observation of the union. -/
theorem positiveCountRead_from_stage [DecidableEq O]
    (original : J) {label : O → T} {region : T → Bool} {allowed : Nat → Prop}
    (read : PositiveCountRead label (⋃ stage, world stage) region allowed) :
    ∃ (stage : J) (_route : original ⟶ stage),
      PositiveCountRead label (world stage) region allowed := by
  obtain ⟨witness, observed⟩ := (positiveCountRead_union_iff world grows).1 read
  exact ⟨IsFiltered.max original witness, IsFiltered.leftToMax original witness,
    positiveCountRead_mono (grows (IsFiltered.rightToMax original witness)) observed⟩

end FilteredGrowth

#print axioms takesBetween_image
#print axioms exact_selected_image_iff_faithful
#print axioms positiveCountRead_finite_iff
#print axioms positiveCountRead_union_iff
#print axioms positiveCountRead_from_stage

end Mettapedia.GSLT.OccurrenceObservationGrowth
