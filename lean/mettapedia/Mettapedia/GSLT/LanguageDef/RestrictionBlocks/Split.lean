import Mettapedia.GSLT.LanguageDef.RestrictionBlocks.Completeness
import Mettapedia.GSLT.LanguageDef.RestrictionBlocks.Molecules

/-!
# Splitting a block along the restrictions its parts use

A block whose components fall into two parts using disjoint sets of its restrictions is the two parts side by side,
each a block over the restrictions it uses (`split_equivalent`). The proof reorders the restrictions so that the
second part's come innermost, the first part's next and the unused ones outermost; drops the unused ones; and reads
the result as the first part's block beside the second's.

This file holds the order that does the reordering (`splitOrder`) and the facts about it.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.RestrictionBlocks

open Mettapedia.OSLF.MeTTaIL.Syntax

/-- **The new place of a restriction**: the second part's restrictions innermost in their order, the first part's
next, every other restriction outermost in increasing order. -/
def splitPlace (count : Nat) (first second : List Nat) (index : Nat) : Nat :=
  if second.contains index then second.idxOf index
  else if first.contains index then second.length + first.idxOf index
  else second.length + first.length +
    ((List.range count).filter fun other => !first.contains other && !second.contains other).idxOf index

/-- The order of the restrictions after the split: restriction `index` goes to `splitPlace index`. -/
def splitOrder (count : Nat) (first second : List Nat) : List Nat :=
  (List.range count).map (splitPlace count first second)

theorem splitOrder_length (count : Nat) (first second : List Nat) : (splitOrder count first second).length = count := by
  simp [splitOrder]

/-- The restrictions neither part uses, in increasing order. -/
def unusedRestrictions (count : Nat) (first second : List Nat) : List Nat :=
  (List.range count).filter fun other => !first.contains other && !second.contains other

/-- **The parts of a split**: two lists of restrictions of a block of `count`, without repeats, sharing none. -/
structure SplitParts (count : Nat) (first second : List Nat) : Prop where
  firstNodup : first.Nodup
  secondNodup : second.Nodup
  firstInside : ∀ index ∈ first, index < count
  secondInside : ∀ index ∈ second, index < count
  disjoint : ∀ index ∈ first, index ∉ second

namespace SplitParts

variable {count : Nat} {first second : List Nat}

theorem unused_nodup (_parts : SplitParts count first second) : (unusedRestrictions count first second).Nodup :=
  (List.nodup_range).filter _

theorem mem_unused {index : Nat} :
    index ∈ unusedRestrictions count first second ↔ index < count ∧ index ∉ first ∧ index ∉ second := by
  simp [unusedRestrictions]

/-- The three lists together hold every restriction exactly once. -/
theorem lengths (parts : SplitParts count first second) :
    second.length + first.length + (unusedRestrictions count first second).length = count := by
  have whole : (second ++ first ++ unusedRestrictions count first second).Perm (List.range count) := by
    apply (List.perm_ext_iff_of_nodup _ List.nodup_range).mpr
    · intro index
      simp only [List.mem_append, mem_unused, List.mem_range]
      constructor
      · rintro ((member | member) | ⟨inside, -, -⟩)
        · exact parts.secondInside index member
        · exact parts.firstInside index member
        · exact inside
      · intro inside
        by_cases inSecond : index ∈ second
        · exact .inl (.inl inSecond)
        · by_cases inFirst : index ∈ first
          · exact .inl (.inr inFirst)
          · exact .inr ⟨inside, inFirst, inSecond⟩
    · refine List.Nodup.append (List.Nodup.append parts.secondNodup parts.firstNodup ?_) parts.unused_nodup ?_
      · intro index inSecond inFirst
        exact parts.disjoint index inFirst inSecond
      · intro index member unused
        rcases List.mem_append.mp member with inSecond | inFirst
        · exact (mem_unused.mp unused).2.2 inSecond
        · exact (mem_unused.mp unused).2.1 inFirst
  have counted := whole.length_eq
  simp only [List.length_append, List.length_range] at counted
  omega

/-- A restriction's new place is a restriction of the block. -/
theorem splitPlace_lt (parts : SplitParts count first second) {index : Nat} (inside : index < count) :
    splitPlace count first second index < count := by
  have total := parts.lengths
  unfold splitPlace
  split_ifs with inSecond inFirst
  · have := List.idxOf_lt_length_of_mem (List.contains_iff_mem.mp inSecond)
    omega
  · have := List.idxOf_lt_length_of_mem (List.contains_iff_mem.mp inFirst)
    omega
  · have member : index ∈ unusedRestrictions count first second :=
      mem_unused.mpr ⟨inside, fun found => inFirst (List.contains_iff_mem.mpr found),
        fun found => inSecond (List.contains_iff_mem.mpr found)⟩
    have := List.idxOf_lt_length_of_mem member
    change second.length + first.length + (unusedRestrictions count first second).idxOf index < count
    omega

/-- Two members of a list at one place are one. -/
theorem eq_of_idxOf_eq {list : List Nat} {left right : Nat} (leftIn : left ∈ list) (rightIn : right ∈ list)
    (same : list.idxOf left = list.idxOf right) : left = right := by
  have leftAt := List.getElem_idxOf (List.idxOf_lt_length_of_mem leftIn)
  have rightAt := List.getElem_idxOf (List.idxOf_lt_length_of_mem rightIn)
  simp only [same] at leftAt
  exact leftAt.symm.trans rightAt

/-- **Distinct restrictions go to distinct places.** -/
theorem splitPlace_injective (parts : SplitParts count first second) {left right : Nat} (leftInside : left < count)
    (rightInside : right < count) (same : splitPlace count first second left = splitPlace count first second right) :
    left = right := by
  have unusedOf : ∀ {index}, index < count → ¬ second.contains index = true → ¬ first.contains index = true →
      index ∈ unusedRestrictions count first second := fun inside notSecond notFirst =>
    mem_unused.mpr ⟨inside, fun found => notFirst (List.contains_iff_mem.mpr found),
      fun found => notSecond (List.contains_iff_mem.mpr found)⟩
  have bound : ∀ {list : List Nat} {index}, list.contains index = true → list.idxOf index < list.length :=
    fun found => List.idxOf_lt_length_of_mem (List.contains_iff_mem.mp found)
  have unusedBound : ∀ {index}, index < count → ¬ second.contains index = true → ¬ first.contains index = true →
      (unusedRestrictions count first second).idxOf index < (unusedRestrictions count first second).length :=
    fun inside notSecond notFirst => List.idxOf_lt_length_of_mem (unusedOf inside notSecond notFirst)
  have total := parts.lengths
  unfold splitPlace at same
  by_cases leftSecond : second.contains left = true
  · by_cases rightSecond : second.contains right = true
    · rw [if_pos leftSecond, if_pos rightSecond] at same
      exact eq_of_idxOf_eq (List.contains_iff_mem.mp leftSecond) (List.contains_iff_mem.mp rightSecond) same
    · have := bound leftSecond
      rw [if_pos leftSecond, if_neg rightSecond] at same
      split_ifs at same <;> omega
  · by_cases rightSecond : second.contains right = true
    · have := bound rightSecond
      rw [if_neg leftSecond, if_pos rightSecond] at same
      split_ifs at same <;> omega
    · rw [if_neg leftSecond, if_neg rightSecond] at same
      by_cases leftFirst : first.contains left = true
      · by_cases rightFirst : first.contains right = true
        · rw [if_pos leftFirst, if_pos rightFirst] at same
          exact eq_of_idxOf_eq (List.contains_iff_mem.mp leftFirst) (List.contains_iff_mem.mp rightFirst)
            (by omega)
        · have := bound leftFirst
          rw [if_pos leftFirst, if_neg rightFirst] at same
          omega
      · by_cases rightFirst : first.contains right = true
        · have := bound rightFirst
          rw [if_neg leftFirst, if_pos rightFirst] at same
          omega
        · rw [if_neg leftFirst, if_neg rightFirst] at same
          exact eq_of_idxOf_eq (unusedOf leftInside leftSecond leftFirst) (unusedOf rightInside rightSecond rightFirst)
            (by change second.length + first.length + (unusedRestrictions count first second).idxOf left =
              second.length + first.length + (unusedRestrictions count first second).idxOf right at same; omega)

/-- **The split order is an order of the restrictions.** -/
theorem splitOrder_perm (parts : SplitParts count first second) :
    (splitOrder count first second).Perm (List.range count) := by
  have nodup : (splitOrder count first second).Nodup := by
    unfold splitOrder
    refine List.Nodup.map_on ?_ List.nodup_range
    intro left leftIn right rightIn same
    exact splitPlace_injective parts (List.mem_range.mp leftIn) (List.mem_range.mp rightIn) same
  have within : splitOrder count first second ⊆ List.range count := by
    intro place member
    obtain ⟨index, inRange, rfl⟩ := List.mem_map.mp member
    exact List.mem_range.mpr (splitPlace_lt parts (List.mem_range.mp inRange))
  exact (nodup.subperm within).perm_of_length_le (by simp [splitOrder_length])

end SplitParts

/-! ## Renaming the parts -/

open Mettapedia.OSLF.MeTTaIL.CanonicalBags (FreeIn)
open Mettapedia.OSLF.MeTTaIL.Substitution (liftBVars)

/-- Lower the indices at and above `cutoff` by `amount`: `amount` unused restrictions just outside a block of
`cutoff` dropped. -/
def lowerAbove (cutoff amount index : Nat) : Nat := if index < cutoff then index else index - amount

theorem splitOrder_getD {count : Nat} {first second : List Nat} {index : Nat} (inside : index < count) :
    (splitOrder count first second).getD index index = splitPlace count first second index := by
  simp [splitOrder, List.getD_eq_getElem?_getD, inside]

variable {count : Nat} {first second : List Nat}

/-- **A component of the first part**, renamed by the split order and with the unused restrictions dropped, is its
own block's component lifted past the second part's restrictions, as a block beside the second part sees it. -/
theorem first_part_renaming (parts : SplitParts count first second) {component : Pattern}
    (uses : ∀ index, FreeIn index component → index < count → index ∈ first) :
    rename (lowerAbove (second.length + first.length) (unusedRestrictions count first second).length)
      (rename (Prenex.permute count (splitOrder count first second)) component) =
    liftBVars 0 second.length (rename (Prenex.groupIndex count first) component) := by
  rw [rename_comp, liftBVars_eq_rename, rename_comp]
  apply rename_congr
  intro index free
  have total := parts.lengths
  simp only [Function.comp_apply, Prenex.permute, Prenex.groupIndex, lowerAbove, shiftAbove]
  by_cases inside : index < count
  · have inFirst := uses index free inside
    have notSecond : ¬ second.contains index = true := fun found =>
      parts.disjoint index inFirst (List.contains_iff_mem.mp found)
    have place : splitPlace count first second index = second.length + first.idxOf index := by
      simp only [splitPlace, if_neg notSecond, if_pos (List.contains_iff_mem.mpr inFirst)]
    have bound := List.idxOf_lt_length_of_mem inFirst
    simp only [if_pos inside, splitOrder_getD inside, place]
    split_ifs <;> omega
  · simp only [if_neg inside]
    split_ifs <;> omega

/-- **A component of the second part**, renamed by the split order and with the unused restrictions dropped, is its
own block's component lifted past the first part's restrictions above the second part's own. -/
theorem second_part_renaming (parts : SplitParts count first second) {component : Pattern}
    (uses : ∀ index, FreeIn index component → index < count → index ∈ second) :
    rename (lowerAbove (second.length + first.length) (unusedRestrictions count first second).length)
      (rename (Prenex.permute count (splitOrder count first second)) component) =
    liftBVars second.length first.length (rename (Prenex.groupIndex count second) component) := by
  rw [rename_comp, liftBVars_eq_rename, rename_comp]
  apply rename_congr
  intro index free
  have total := parts.lengths
  simp only [Function.comp_apply, Prenex.permute, Prenex.groupIndex, lowerAbove, shiftAbove]
  by_cases inside : index < count
  · have inSecond := uses index free inside
    have place : splitPlace count first second index = second.idxOf index := by
      simp only [splitPlace, if_pos (List.contains_iff_mem.mpr inSecond)]
    have bound := List.idxOf_lt_length_of_mem inSecond
    simp only [if_pos inside, splitOrder_getD inside, place]
    split_ifs <;> omega
  · simp only [if_neg inside]
    split_ifs <;> omega

/-! ## Dropping the unused restrictions -/

section Drop

variable {language : LanguageDef} {block : Block} [laws : BlockSignature language block]

open Mettapedia.GSLT.LanguageDef.WellSorted (HasType FreeTypeContext)

/-- **Unused outermost restrictions drop**: a block whose outermost `amount` restrictions no component uses is the
block without them, the names outside it moved down past them. -/
theorem drop_outer_equivalent {free : FreeTypeContext} {bound : List TypeExpr} (kept : Nat) :
    ∀ (amount : Nat) {components : List Pattern},
      Members language block free (List.replicate (kept + amount) (TypeExpr.base block.name) ++ bound) components →
      (∀ component ∈ components, ∀ index, kept ≤ index → index < kept + amount → ¬ FreeIn index component) →
      Members language block free (List.replicate kept (TypeExpr.base block.name) ++ bound)
          (components.map (rename (lowerAbove kept amount))) ∧
        ProcEquiv language block free bound (Prenex.toPattern block ⟨kept + amount, components⟩)
          (Prenex.toPattern block ⟨kept, components.map (rename (lowerAbove kept amount))⟩)
  | 0, components, members, _ => by
      have same : components.map (rename (lowerAbove kept 0)) = components := by
        have identity : lowerAbove kept 0 = id := by
          funext index
          simp only [lowerAbove, Nat.sub_zero, id]
          split_ifs <;> rfl
        rw [identity]
        conv_rhs => rw [← List.map_id components]
        exact List.map_congr_left fun component _ => rename_id component
      rw [same]
      exact ⟨by simpa using members, .refl _⟩
  | amount + 1, components, members, unused => by
      have outermost : ∀ component ∈ components, ¬ FreeIn (kept + amount) component :=
        fun component member => unused component member _ (by omega) (by omega)
      have inner : Members language block free
          (List.replicate (kept + amount) (TypeExpr.base block.name) ++ (TypeExpr.base block.name :: bound))
          components := by
        simpa [← Nat.add_assoc, List.replicate_succ', List.append_assoc] using members
      have dropped : Prenex.close ⟨kept + amount, components⟩ =
          ⟨kept + amount, components.map (rename (dropIndex (kept + amount)))⟩ := by
        simp only [Prenex.close]
        rw [if_neg]
        intro anyUsed
        obtain ⟨component, member, used⟩ := List.any_eq_true.mp anyUsed
        exact outermost component member ((mentions_iff component _).mp used)
      have closed := close_sound (form := ⟨kept + amount, components⟩) inner
      rw [dropped] at closed
      obtain ⟨closedMembers, closedEquivalent⟩ := closed
      have stillUnused : ∀ component ∈ components.map (rename (dropIndex (kept + amount))), ∀ index, kept ≤ index →
          index < kept + amount → ¬ FreeIn index component := by
        intro component member index low high freeHere
        obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp member
        obtain ⟨source, sourceFree, moved⟩ := (freeIn_rename original).mp freeHere
        simp only [dropIndex] at moved
        split_ifs at moved with below
        · exact unused original originalMember source (by omega) (by omega) sourceFree
        · have : source = kept + amount := by omega
          exact outermost original originalMember (this ▸ sourceFree)
      obtain ⟨restMembers, restEquivalent⟩ := drop_outer_equivalent kept amount closedMembers stillUnused
      have composed : (components.map (rename (dropIndex (kept + amount)))).map (rename (lowerAbove kept amount)) =
          components.map (rename (lowerAbove kept (amount + 1))) := by
        rw [List.map_map]
        apply List.map_congr_left
        intro component member
        show rename _ (rename _ component) = _
        rw [rename_comp]
        apply rename_congr
        intro index freeHere
        simp only [Function.comp_apply, dropIndex, lowerAbove]
        by_cases low : index < kept
        · simp [low, show index < kept + amount by omega]
        · by_cases high : index < kept + (amount + 1)
          · exact absurd freeHere (unused component member index (by omega) high)
          · split_ifs <;> omega
      rw [composed] at restMembers restEquivalent
      refine ⟨restMembers, ?_⟩
      have shape : Prenex.toPattern block ⟨kept + (amount + 1), components⟩ =
          .apply block.restrict [.lambda none (Prenex.toPattern block ⟨kept + amount, components⟩)] := by
        simp only [Prenex.toPattern, ← Nat.add_assoc, Prenex.restricts_succ]
      rw [shape]
      exact .trans _ _ _ closedEquivalent restEquivalent

omit laws in
/-- **Renaming keeps a pattern's type** when it keeps the sort of every variable the pattern uses. -/
theorem rename_typed_on_support {free : FreeTypeContext} {source target : List TypeExpr} {pattern : Pattern}
    {type : TypeExpr} {relabel : Nat → Nat} (typed : HasType language free source pattern type)
    (sorts : ∀ index sort, FreeIn index pattern → source[index]? = some sort → target[relabel index]? = some sort) :
    HasType language free target (rename relabel pattern) type :=
  Mettapedia.GSLT.LanguageDef.WellSorted.HasType.substituteBoundOnSupport typed (fun index => .bvar (relabel index))
    (fun index sort used lookup =>
      Mettapedia.GSLT.LanguageDef.WellSorted.HasType.bvar (sorts index sort (freeIn_of_uses used) lookup))

omit laws in
/-- **A part of a block, read as a block of its own, is typed** where the block's components are. -/
theorem part_members {free : FreeTypeContext} {bound : List TypeExpr} {count : Nat} {restrictions : List Nat}
    {part : List Pattern}
    (members : Members language block free (List.replicate count (TypeExpr.base block.name) ++ bound) part)
    (uses : ∀ component ∈ part, ∀ index, FreeIn index component → index < count → index ∈ restrictions) :
    Members language block free (List.replicate restrictions.length (TypeExpr.base block.name) ++ bound)
      (part.map (rename (Prenex.groupIndex count restrictions))) := by
  intro element member
  obtain ⟨component, componentMember, rfl⟩ := List.mem_map.mp member
  apply rename_typed_on_support (members component componentMember)
  intro index sort freeHere lookup
  simp only [Prenex.groupIndex]
  by_cases below : index < count
  · have listed := uses component componentMember index freeHere below
    have position := List.idxOf_lt_length_of_mem listed
    rw [if_pos below]
    rw [List.getElem?_append_left (by simpa using below), List.getElem?_replicate] at lookup
    rw [List.getElem?_append_left (by simpa using position), List.getElem?_replicate]
    simpa [below, position] using lookup
  · rw [if_neg below]
    rw [List.getElem?_append_right (by simpa using Nat.le_of_not_lt below)] at lookup
    rw [List.getElem?_append_right (by simp), List.length_replicate]
    simpa [Nat.add_sub_cancel] using lookup

/-- **A block splits along the restrictions its parts use**: when one part of the components uses only the
restrictions `first` and the other only `second`, the two lists sharing none, the block is the two parts side by
side, each a block over its own restrictions in their order, the unused restrictions dropped. -/
theorem split_equivalent {free : FreeTypeContext} {bound : List TypeExpr} {count : Nat} {first second : List Nat}
    (parts : SplitParts count first second) {partOne partTwo : List Pattern}
    (members : Members language block free (List.replicate count (TypeExpr.base block.name) ++ bound)
      (partOne ++ partTwo))
    (oneUses : ∀ component ∈ partOne, ∀ index, FreeIn index component → index < count → index ∈ first)
    (twoUses : ∀ component ∈ partTwo, ∀ index, FreeIn index component → index < count → index ∈ second) :
    ProcEquiv language block free bound (Prenex.toPattern block ⟨count, partOne ++ partTwo⟩)
      (.collection .hashBag
        [Prenex.toPattern block ⟨first.length, partOne.map (rename (Prenex.groupIndex count first))⟩,
          Prenex.toPattern block ⟨second.length, partTwo.map (rename (Prenex.groupIndex count second))⟩] none) := by
  have reorders : Reorders (List.range count) (splitOrder count first second) :=
    orders_reorders (List.range count) _ (orders_complete _ _ parts.splitOrder_perm)
  obtain ⟨reordered, reorderEquivalent⟩ := block_reorder_equivalent reorders members
  have total := parts.lengths
  have unused : ∀ component ∈ (partOne ++ partTwo).map (rename (Prenex.permute count (splitOrder count first second))),
      ∀ index, second.length + first.length ≤ index →
        index < second.length + first.length + (unusedRestrictions count first second).length →
          ¬ FreeIn index component := by
    intro component member index low high freeHere
    obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp member
    obtain ⟨source, sourceFree, moved⟩ := (freeIn_rename original).mp freeHere
    simp only [Prenex.permute] at moved
    split_ifs at moved with sourceInside
    · rw [splitOrder_getD sourceInside] at moved
      rcases List.mem_append.mp originalMember with inOne | inTwo
      · have inFirst := oneUses original inOne source sourceFree sourceInside
        have notSecond : ¬ second.contains source = true := fun found =>
          parts.disjoint source inFirst (List.contains_iff_mem.mp found)
        have place : splitPlace count first second source = second.length + first.idxOf source := by
          simp only [splitPlace, if_neg notSecond, if_pos (List.contains_iff_mem.mpr inFirst)]
        have := List.idxOf_lt_length_of_mem inFirst
        omega
      · have inSecond := twoUses original inTwo source sourceFree sourceInside
        have place : splitPlace count first second source = second.idxOf source := by
          simp only [splitPlace, if_pos (List.contains_iff_mem.mpr inSecond)]
        have := List.idxOf_lt_length_of_mem inSecond
        omega
    · omega
  have reordered' : Members language block free
      (List.replicate (second.length + first.length + (unusedRestrictions count first second).length)
        (TypeExpr.base block.name) ++ bound)
      ((partOne ++ partTwo).map (rename (Prenex.permute count (splitOrder count first second)))) := by
    rw [total]; exact reordered
  obtain ⟨-, dropEquivalent⟩ := drop_outer_equivalent _ _ reordered' unused
  have components :
      ((partOne ++ partTwo).map (rename (Prenex.permute count (splitOrder count first second)))).map
          (rename (lowerAbove (second.length + first.length) (unusedRestrictions count first second).length)) =
        (Prenex.par ⟨first.length, partOne.map (rename (Prenex.groupIndex count first))⟩
          ⟨second.length, partTwo.map (rename (Prenex.groupIndex count second))⟩).components := by
    simp only [Prenex.par, List.map_append, List.map_map]
    congr 1
    · apply List.map_congr_left
      intro component member
      exact first_part_renaming parts (oneUses component member)
    · apply List.map_congr_left
      intro component member
      exact second_part_renaming parts (twoUses component member)
  have oneMembers := part_members (restrictions := first)
    (fun element member => members element (List.mem_append_left _ member)) oneUses
  have twoMembers := part_members (restrictions := second)
    (fun element member => members element (List.mem_append_right _ member)) twoUses
  have sideBySide := par_equivalent (first := ⟨first.length, partOne.map (rename (Prenex.groupIndex count first))⟩)
    (second := ⟨second.length, partTwo.map (rename (Prenex.groupIndex count second))⟩) oneMembers twoMembers
  have sameCount : Prenex.toPattern block
      ⟨count, (partOne ++ partTwo).map (rename (Prenex.permute count (splitOrder count first second)))⟩ =
      Prenex.toPattern block ⟨second.length + first.length + (unusedRestrictions count first second).length,
        (partOne ++ partTwo).map (rename (Prenex.permute count (splitOrder count first second)))⟩ := by
    rw [total]
  have parShape : Prenex.toPattern block ⟨second.length + first.length,
      ((partOne ++ partTwo).map (rename (Prenex.permute count (splitOrder count first second)))).map
        (rename (lowerAbove (second.length + first.length) (unusedRestrictions count first second).length))⟩ =
      Prenex.toPattern block (Prenex.par ⟨first.length, partOne.map (rename (Prenex.groupIndex count first))⟩
        ⟨second.length, partTwo.map (rename (Prenex.groupIndex count second))⟩) := by
    rw [components]
    simp only [Prenex.par, Nat.add_comm second.length first.length]
  rw [sameCount] at reorderEquivalent
  rw [parShape] at dropEquivalent
  exact .trans _ _ _ reorderEquivalent (.trans _ _ _ dropEquivalent (.symm _ _ sideBySide))

end Drop

/-! ## Controls -/

/-- Two restrictions, the first part using `1` and the second `0`: they stay where they are. -/
example : splitOrder 2 [1] [0] = [0, 1] := by decide

/-- The first part using `0` and the second `1`: they exchange. -/
example : splitOrder 2 [0] [1] = [1, 0] := by decide

/-- An unused restriction goes outermost. -/
example : splitOrder 3 [2] [0] = [0, 2, 1] := by decide

end Mettapedia.GSLT.LanguageDef.RestrictionBlocks
