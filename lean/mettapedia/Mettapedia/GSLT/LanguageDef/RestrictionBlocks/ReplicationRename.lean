import Mettapedia.GSLT.LanguageDef.RestrictionBlocks.ReplicationRestrict

/-!
# A block read through a renaming of its names

A renaming that is injective and keeps a block's restrictions among restrictions and its other names outside
(`Preserving`) carries a group of the block to a group of the renamed block owning the images of its restrictions
(`mem_restrictions_rename`). The renamed group's copy is the original copy with its free names renamed
(`copyRelabel`) and its restrictions reordered (`copyOrder`): `split_comp` says so of every index, and
`groupIndex_comp` of the names a replicated argument reads.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.RestrictionBlocks

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.CanonicalBags (FreeIn liftIndex)

/-- **A renaming keeping a block's restrictions**: injective, the restrictions of a block of `count` to restrictions
of one of `count'`, the other names to other names. -/
structure Preserving (count count' : Nat) (relabel : Nat → Nat) : Prop where
  injective : Function.Injective relabel
  below : ∀ index < count, relabel index < count'
  above : ∀ index, count ≤ index → count' ≤ relabel index

/-- A renamed pattern mentions only images of what it mentioned. -/
theorem mentions_rename_image {relabel : Nat → Nat} (component : Pattern) {index' : Nat}
    (mentioned : mentions index' (rename relabel component) = true) :
    ∃ index, relabel index = index' ∧ mentions index component = true := by
  rw [mentions_iff, freeIn_rename] at mentioned
  obtain ⟨original, free, same⟩ := mentioned
  exact ⟨original, same, (mentions_iff _ _).mpr free⟩

/-- An injective renaming mentions an image exactly where the original mentioned. -/
theorem mentions_rename_injective {relabel : Nat → Nat} (injective : Function.Injective relabel)
    (component : Pattern) (index : Nat) :
    mentions (relabel index) (rename relabel component) = mentions index component := by
  apply Bool.eq_iff_iff.mpr
  rw [mentions_iff, mentions_iff, freeIn_rename]
  constructor
  · rintro ⟨original, free, same⟩
    rwa [← injective same]
  · intro free
    exact ⟨index, free, rfl⟩

namespace Preserving

variable {count count' : Nat} {relabel : Nat → Nat}

theorem lt_iff (preserving : Preserving count count' relabel) {index : Nat} :
    relabel index < count' ↔ index < count := by
  constructor
  · intro below
    by_contra notBelow
    have := preserving.above index (Nat.le_of_not_lt notBelow)
    omega
  · exact preserving.below index

/-- **The restrictions a renamed group owns are the images of the original's.** -/
theorem mem_restrictions_rename (preserving : Preserving count count' relabel) {value : Nat → Pattern}
    {component : Pattern} {items : List Nat} {index' : Nat} :
    index' ∈ restrictionsOf (allowedFor count' (rename relabel component)) count'
        (fun item => rename relabel (value item)) items ↔
      ∃ index ∈ restrictionsOf (allowedFor count component) count value items, relabel index = index' := by
  rw [mem_restrictionsOf]
  constructor
  · rintro ⟨item, inItems, listed⟩
    unfold throughKeys at listed
    obtain ⟨used, allowed⟩ := List.mem_filter.mp listed
    obtain ⟨below', mentioned'⟩ := mem_usedRestrictions.mp used
    obtain ⟨index, rfl, mentioned⟩ := mentions_rename_image (value item) mentioned'
    have below := preserving.lt_iff.mp below'
    refine ⟨index, mem_restrictionsOf.mpr ⟨item, inItems, ?_⟩, rfl⟩
    unfold throughKeys
    refine List.mem_filter.mpr ⟨mem_usedRestrictions.mpr ⟨below, mentioned⟩, ?_⟩
    simp only [allowedFor, List.contains_iff_mem, List.mem_filter, List.mem_range, Bool.not_eq_true'] at allowed ⊢
    rw [mentions_rename_injective preserving.injective] at allowed
    exact ⟨below, allowed.2⟩
  · rintro ⟨index, listed, rfl⟩
    obtain ⟨item, inItems, keyed⟩ := mem_restrictionsOf.mp listed
    unfold throughKeys at keyed
    obtain ⟨used, allowed⟩ := List.mem_filter.mp keyed
    obtain ⟨below, mentioned⟩ := mem_usedRestrictions.mp used
    refine ⟨item, inItems, ?_⟩
    unfold throughKeys
    refine List.mem_filter.mpr ⟨mem_usedRestrictions.mpr ⟨preserving.below index below, by
      rw [mentions_rename_injective preserving.injective]; exact mentioned⟩, ?_⟩
    simp only [allowedFor, List.contains_iff_mem, List.mem_filter, List.mem_range, Bool.not_eq_true'] at allowed ⊢
    rw [mentions_rename_injective preserving.injective]
    exact ⟨preserving.below index below, allowed.2⟩

end Preserving

/-! ## Where a split order sends an index -/

theorem permute_split_inside {count : Nat} {restrictions : List Nat} {index : Nat} (member : index ∈ restrictions)
    (inside : index < count) :
    Prenex.permute count (splitOrder count (outsideOf count restrictions) restrictions) index =
      restrictions.idxOf index := by
  rw [Prenex.permute, if_pos inside, splitOrder_getD inside, splitPlace, if_pos (List.contains_iff_mem.mpr member)]

theorem permute_split_outside {count : Nat} {restrictions : List Nat} {index : Nat} (notMember : index ∉ restrictions)
    (inside : index < count) :
    Prenex.permute count (splitOrder count (outsideOf count restrictions) restrictions) index =
      restrictions.length + (outsideOf count restrictions).idxOf index := by
  rw [Prenex.permute, if_pos inside, splitOrder_getD inside, splitPlace,
    if_neg (fun found => notMember (List.contains_iff_mem.mp found)),
    if_pos (List.contains_iff_mem.mpr (mem_outsideOf.mpr ⟨inside, notMember⟩))]

theorem permute_split_above {count : Nat} {restrictions : List Nat} {index : Nat} (above : count ≤ index) :
    Prenex.permute count (splitOrder count (outsideOf count restrictions) restrictions) index = index := by
  rw [Prenex.permute, if_neg (by omega)]

theorem groupIndex_below {count : Nat} {kept : List Nat} {index : Nat} (inside : index < count) :
    Prenex.groupIndex count kept index = kept.idxOf index := if_pos inside

theorem groupIndex_above {count : Nat} {kept : List Nat} {index : Nat} (above : count ≤ index) :
    Prenex.groupIndex count kept index = index - count + kept.length := if_neg (by omega)

/-- The restrictions outside a list of them number the rest. -/
theorem outsideOf_length {count : Nat} {restrictions : List Nat} (nodup : restrictions.Nodup)
    (inside : ∀ index ∈ restrictions, index < count) :
    (outsideOf count restrictions).length = count - restrictions.length := by
  have parts := outside_parts nodup inside
  have total := parts.lengths
  have empty : unusedRestrictions count (outsideOf count restrictions) restrictions = [] := by
    rw [List.eq_nil_iff_forall_not_mem]
    intro index member
    obtain ⟨below, notOutside, notMember⟩ := SplitParts.mem_unused.mp member
    exact notOutside (mem_outsideOf.mpr ⟨below, notMember⟩)
  rw [empty, List.length_nil] at total
  omega

/-! ## A group's restrictions and their images -/

/-- **A group's restrictions and their images** under a renaming keeping restrictions. -/
structure ImageOf (count count' : Nat) (relabel : Nat → Nat) (restrictions restrictions' : List Nat) : Prop where
  nodup : restrictions.Nodup
  nodup' : restrictions'.Nodup
  inside : ∀ index ∈ restrictions, index < count
  inside' : ∀ index ∈ restrictions', index < count'
  mem_iff : ∀ index', index' ∈ restrictions' ↔ ∃ index ∈ restrictions, relabel index = index'

/-- **The free names of a group's copy, renamed**: the restrictions outside the group to their places among those
outside the renamed group, the names outside the block through the renaming. -/
def copyRelabel (count count' : Nat) (relabel : Nat → Nat) (restrictions restrictions' : List Nat) (index : Nat) :
    Nat :=
  if index < count - restrictions.length then
    (outsideOf count' restrictions').idxOf (relabel ((outsideOf count restrictions).getD index 0))
  else relabel (index + restrictions.length) - restrictions.length

/-- **The order of a group's restrictions in the renamed block.** -/
def copyOrder (relabel : Nat → Nat) (restrictions restrictions' : List Nat) : List Nat :=
  restrictions.map fun index => restrictions'.idxOf (relabel index)

namespace ImageOf

variable {count count' : Nat} {relabel : Nat → Nat} {restrictions restrictions' : List Nat}

theorem perm_map (image : ImageOf count count' relabel restrictions restrictions')
    (preserving : Preserving count count' relabel) : restrictions'.Perm (restrictions.map relabel) := by
  refine (List.perm_ext_iff_of_nodup image.nodup' (image.nodup.map preserving.injective)).mpr fun index' => ?_
  rw [image.mem_iff, List.mem_map]

theorem length_eq (image : ImageOf count count' relabel restrictions restrictions')
    (preserving : Preserving count count' relabel) : restrictions'.length = restrictions.length := by
  rw [(image.perm_map preserving).length_eq, List.length_map]

theorem not_mem_image (image : ImageOf count count' relabel restrictions restrictions')
    (preserving : Preserving count count' relabel) {index : Nat} (notMember : index ∉ restrictions) :
    relabel index ∉ restrictions' := by
  rw [image.mem_iff]
  rintro ⟨other, member, same⟩
  exact notMember (preserving.injective same ▸ member)

theorem length_le (image : ImageOf count count' relabel restrictions restrictions') :
    restrictions.length ≤ count := length_le_of_inside image.nodup image.inside

theorem length_le' (image : ImageOf count count' relabel restrictions restrictions') :
    restrictions'.length ≤ count' := length_le_of_inside image.nodup' image.inside'

/-- The renamed copy reads an outside restriction at the place of its image. -/
theorem copyRelabel_outside (image : ImageOf count count' relabel restrictions restrictions') {index : Nat}
    (inside : index < count) (notMember : index ∉ restrictions) :
    copyRelabel count count' relabel restrictions restrictions' ((outsideOf count restrictions).idxOf index) =
      (outsideOf count' restrictions').idxOf (relabel index) := by
  have member : index ∈ outsideOf count restrictions := mem_outsideOf.mpr ⟨inside, notMember⟩
  have placed := List.idxOf_lt_length_of_mem member
  rw [outsideOf_length image.nodup image.inside] at placed
  rw [copyRelabel, if_pos placed, List.getD_eq_getElem _ _ (List.idxOf_lt_length_of_mem member),
    List.getElem_idxOf]

/-- The renamed copy reads a name outside the block through the renaming. -/
theorem copyRelabel_above (image : ImageOf count count' relabel restrictions restrictions') {index : Nat}
    (above : count ≤ index) :
    copyRelabel count count' relabel restrictions restrictions' (index - restrictions.length) =
      relabel index - restrictions.length := by
  have small := image.length_le
  rw [copyRelabel, if_neg (by omega), Nat.sub_add_cancel (by omega)]

theorem copyRelabel_injective (image : ImageOf count count' relabel restrictions restrictions')
    (preserving : Preserving count count' relabel) :
    Function.Injective (copyRelabel count count' relabel restrictions restrictions') := by
  have lengthEq := image.length_eq preserving
  have small := image.length_le
  have small' := image.length_le'
  have outsideLength := outsideOf_length image.nodup image.inside
  have outsideLength' := outsideOf_length image.nodup' image.inside'
  -- an outside restriction's image is outside the renamed group
  have imageOutside : ∀ position < count - restrictions.length,
      relabel ((outsideOf count restrictions).getD position 0) ∈ outsideOf count' restrictions' := by
    intro position below
    have inRange : position < (outsideOf count restrictions).length := by omega
    have member : (outsideOf count restrictions).getD position 0 ∈ outsideOf count restrictions := by
      rw [List.getD_eq_getElem _ _ inRange]
      exact List.getElem_mem inRange
    obtain ⟨inside, notMember⟩ := mem_outsideOf.mp member
    exact mem_outsideOf.mpr ⟨preserving.below _ inside, image.not_mem_image preserving notMember⟩
  have bigAbove : ∀ position, ¬ position < count - restrictions.length →
      count' ≤ relabel (position + restrictions.length) := fun position notBelow =>
    preserving.above _ (by omega)
  intro first second same
  unfold copyRelabel at same
  by_cases firstBelow : first < count - restrictions.length <;>
    by_cases secondBelow : second < count - restrictions.length
  · rw [if_pos firstBelow, if_pos secondBelow] at same
    have equalImages := SplitParts.eq_of_idxOf_eq (imageOutside first firstBelow) (imageOutside second secondBelow) same
    have equalPlaces := preserving.injective equalImages
    have firstIn : first < (outsideOf count restrictions).length := by omega
    have secondIn : second < (outsideOf count restrictions).length := by omega
    rw [List.getD_eq_getElem _ _ firstIn, List.getD_eq_getElem _ _ secondIn] at equalPlaces
    exact (List.Nodup.getElem_inj_iff ((List.nodup_range).filter _)).mp equalPlaces
  · rw [if_pos firstBelow, if_neg secondBelow] at same
    have placed := List.idxOf_lt_length_of_mem (imageOutside first firstBelow)
    have big := bigAbove second secondBelow
    omega
  · rw [if_neg firstBelow, if_pos secondBelow] at same
    have placed := List.idxOf_lt_length_of_mem (imageOutside second secondBelow)
    have big := bigAbove first firstBelow
    omega
  · rw [if_neg firstBelow, if_neg secondBelow] at same
    have bigFirst := bigAbove first firstBelow
    have bigSecond := bigAbove second secondBelow
    have equal := preserving.injective (show relabel (first + restrictions.length) =
      relabel (second + restrictions.length) by omega)
    omega

/-- **The renamed group's restrictions are the original's in another order.** -/
theorem copyOrder_isOrder (image : ImageOf count count' relabel restrictions restrictions')
    (preserving : Preserving count count' relabel) :
    IsOrder restrictions.length (copyOrder relabel restrictions restrictions') := by
  have lengthEq := image.length_eq preserving
  unfold IsOrder copyOrder
  refine (List.perm_ext_iff_of_nodup ?_ List.nodup_range).mpr fun position => ?_
  · refine image.nodup.map_on fun first inFirst second inSecond same => ?_
    have firstImage := (image.mem_iff (relabel first)).mpr ⟨first, inFirst, rfl⟩
    have secondImage := (image.mem_iff (relabel second)).mpr ⟨second, inSecond, rfl⟩
    exact preserving.injective (SplitParts.eq_of_idxOf_eq firstImage secondImage same)
  · rw [List.mem_map, List.mem_range]
    constructor
    · rintro ⟨index, member, rfl⟩
      rw [← lengthEq]
      exact List.idxOf_lt_length_of_mem ((image.mem_iff _).mpr ⟨index, member, rfl⟩)
    · intro below
      rw [← lengthEq] at below
      obtain ⟨index, member, same⟩ := (image.mem_iff _).mp (List.getElem_mem below)
      refine ⟨index, member, ?_⟩
      rw [same, image.nodup'.idxOf_getElem _ below]

/-- **Every index of the renamed copy**: the renamed group's split order after the renaming is the original split
order, then the copy's free names renamed, then its restrictions reordered. -/
theorem split_comp (image : ImageOf count count' relabel restrictions restrictions')
    (preserving : Preserving count count' relabel) (index : Nat) :
    Prenex.permute count' (splitOrder count' (outsideOf count' restrictions') restrictions') (relabel index) =
      Prenex.permute restrictions.length (copyOrder relabel restrictions restrictions')
        (liftIndex restrictions.length (copyRelabel count count' relabel restrictions restrictions')
          (Prenex.permute count (splitOrder count (outsideOf count restrictions) restrictions) index)) := by
  have lengthEq := image.length_eq preserving
  have small := image.length_le
  have small' := image.length_le'
  by_cases inside : index < count
  · by_cases member : index ∈ restrictions
    · have imageMember := (image.mem_iff (relabel index)).mpr ⟨index, member, rfl⟩
      have placed := List.idxOf_lt_length_of_mem member
      rw [permute_split_inside imageMember (preserving.below index inside), permute_split_inside member inside,
        liftIndex, if_pos placed, Prenex.permute, if_pos placed, copyOrder,
        List.getD_eq_getElem _ _ (by simpa using placed), List.getElem_map, List.getElem_idxOf]
    · have imageNot := image.not_mem_image preserving member
      rw [permute_split_outside imageNot (preserving.below index inside), permute_split_outside member inside,
        liftIndex, if_neg (by omega), Nat.add_sub_cancel_left, image.copyRelabel_outside inside member,
        Prenex.permute, if_neg (by omega), lengthEq]
      omega
  · have above : count ≤ index := Nat.le_of_not_lt inside
    have imageAbove := preserving.above index above
    rw [permute_split_above imageAbove, permute_split_above above, liftIndex, if_neg (by omega),
      image.copyRelabel_above above, Prenex.permute, if_neg (by omega)]
    omega

/-- **The names a replicated argument reads**, renumbered for the renamed copy, are its renumbering for the original
copy, renamed. -/
theorem groupIndex_comp (image : ImageOf count count' relabel restrictions restrictions')
    (preserving : Preserving count count' relabel) {index : Nat} (outside : index < count → index ∉ restrictions) :
    Prenex.groupIndex count' (outsideOf count' restrictions') (relabel index) =
      copyRelabel count count' relabel restrictions restrictions'
        (Prenex.groupIndex count (outsideOf count restrictions) index) := by
  have lengthEq := image.length_eq preserving
  have small := image.length_le
  have small' := image.length_le'
  by_cases inside : index < count
  · rw [groupIndex_below (preserving.below index inside), groupIndex_below inside,
      image.copyRelabel_outside inside (outside inside)]
  · have above : count ≤ index := Nat.le_of_not_lt inside
    have imageAbove := preserving.above index above
    rw [groupIndex_above imageAbove, groupIndex_above above, outsideOf_length image.nodup' image.inside',
      outsideOf_length image.nodup image.inside, lengthEq,
      show index - count + (count - restrictions.length) = index - restrictions.length by omega,
      image.copyRelabel_above above]
    omega

end ImageOf

/-! ## A block read back -/

/-- Every restriction of a block is mentioned by one of its components. -/
def Prenex.Used (form : Prenex) : Prop :=
  ∀ index < form.count, ∃ component ∈ form.components, mentions index component = true

/-- Every component of a block is its own block. -/
def Prenex.Atomic (block : Block) (form : Prenex) : Prop :=
  ∀ component ∈ form.components, decompose block component = Prenex.atom component

theorem decompose_body {block : Block} {components : List Pattern}
    (atomic : ∀ component ∈ components, decompose block component = Prenex.atom component) :
    decompose block (Prenex.body block components) = ⟨0, components⟩ := by
  match components, atomic with
  | [], _ => exact decompose_unit block
  | [component], atomic => exact atomic component (List.mem_singleton_self _)
  | first :: second :: rest, atomic =>
      rw [show Prenex.body block (first :: second :: rest) = .collection .hashBag (first :: second :: rest) none
        from rfl, decompose_bag, decomposeList_atoms atomic]

theorem decompose_restricts_atoms {block : Block} {components : List Pattern}
    (atomic : ∀ component ∈ components, decompose block component = Prenex.atom component) :
    ∀ (count : Nat), (∀ index < count, components.any (mentions index) = true) →
      decompose block (Prenex.restricts block count (Prenex.body block components)) = ⟨count, components⟩
  | 0, _ => decompose_body atomic
  | count + 1, used => by
      rw [Prenex.restricts_succ, decompose_restrict,
        decompose_restricts_atoms atomic count fun index below => used index (by omega)]
      unfold Prenex.close
      rw [if_pos (used count (by omega))]
      rfl

/-- **A block of atoms, every restriction used, is the block of its pattern.** -/
theorem decompose_toPattern {block : Block} {form : Prenex} (atomic : form.Atomic block) (used : form.Used) :
    decompose block (Prenex.toPattern block form) = form := by
  obtain ⟨count, components⟩ := form
  exact decompose_restricts_atoms atomic count fun index below => by
    obtain ⟨component, member, mentioned⟩ := used index below
    exact List.any_eq_true.mpr ⟨component, member, mentioned⟩

/-- A renamed atom is an atom. -/
theorem atomic_rename {block : Block} {component : Pattern} (atomic : decompose block component = Prenex.atom component)
    (relabel : Nat → Nat) : decompose block (rename relabel component) = Prenex.atom (rename relabel component) := by
  rw [decompose_renameOuter, atomic, atom_renameOuter]

theorem atomic_map_rename {block : Block} {components : List Pattern}
    (atomic : ∀ component ∈ components, decompose block component = Prenex.atom component) (relabel : Nat → Nat) :
    ∀ component ∈ components.map (rename relabel), decompose block component = Prenex.atom component := by
  intro component member
  obtain ⟨original, inOriginal, rfl⟩ := List.mem_map.mp member
  exact atomic_rename (atomic original inOriginal) relabel

/-- A renaming fixing a block's restrictions keeps them used. -/
theorem used_rename {count : Nat} {components : List Pattern} (used : (Prenex.mk count components).Used)
    {relabel : Nat → Nat} (fixed : ∀ index < count, relabel index = index) :
    (Prenex.mk count (components.map (rename relabel))).Used := by
  intro index below
  obtain ⟨component, member, mentioned⟩ := used index below
  refine ⟨rename relabel component, List.mem_map_of_mem member, ?_⟩
  rw [mentions_iff, freeIn_rename]
  exact ⟨index, (mentions_iff _ _).mp mentioned, fixed index below⟩

/-- Reordering a block's restrictions keeps them used. -/
theorem used_permute {count : Nat} {components : List Pattern} (used : (Prenex.mk count components).Used)
    {order : List Nat} (isOrder : IsOrder count order) :
    (Prenex.mk count (components.map (rename (Prenex.permute count order)))).Used := by
  intro index below
  have inOrder : index ∈ order := isOrder.symm.subset (List.mem_range.mpr below)
  obtain ⟨position, inside, atPosition⟩ := List.mem_iff_getElem.mp inOrder
  have positionBelow : position < count := by
    have := isOrder.length_eq
    simp only [List.length_range] at this
    omega
  obtain ⟨component, member, mentioned⟩ := used position positionBelow
  refine ⟨rename (Prenex.permute count order) component, List.mem_map_of_mem member, ?_⟩
  rw [mentions_iff, freeIn_rename]
  refine ⟨position, (mentions_iff _ _).mp mentioned, ?_⟩
  rw [Prenex.permute, if_pos positionBelow, List.getD_eq_getElem _ _ inside, atPosition]

/-! ## A group of the renamed block -/

variable {block : ReplicationBlock}

theorem placeValue_map_rename (relabel : Nat → Nat) (components : List Pattern) (place : Nat) :
    placeValue block (components.map (rename relabel)) place = rename relabel (placeValue block components place) := by
  unfold placeValue
  have unitFixed : rename relabel (Pattern.apply block.unit []) = .apply block.unit [] := by
    rw [rename_apply]
    rfl
  conv_lhs => rw [← unitFixed]
  rw [List.getD_map]

theorem restrictionsOf_nodup (allowed : List Nat) (count : Nat) (value : Nat → Pattern) (items : List Nat) :
    (restrictionsOf allowed count value items).Nodup := by
  unfold restrictionsOf
  exact List.nodup_range.filter _

theorem restrictionsOf_lt {allowed : List Nat} {count : Nat} {value : Nat → Pattern} {items : List Nat}
    {index : Nat} (member : index ∈ restrictionsOf allowed count value items) : index < count := by
  obtain ⟨_, _, keyed⟩ := mem_restrictionsOf.mp member
  exact throughKeys_lt keyed

/-- A group's restrictions are allowed. -/
theorem restrictionsOf_allowed {allowed : List Nat} {count : Nat} {value : Nat → Pattern} {items : List Nat}
    {index : Nat} (member : index ∈ restrictionsOf allowed count value items) : index ∈ allowed := by
  obtain ⟨_, _, keyed⟩ := mem_restrictionsOf.mp member
  unfold throughKeys at keyed
  exact List.contains_iff_mem.mp (List.mem_filter.mp keyed).2

theorem imageOf_rename {count count' : Nat} {relabel : Nat → Nat} (preserving : Preserving count count' relabel)
    (value : Nat → Pattern) (component : Pattern) (items : List Nat) :
    ImageOf count count' relabel (restrictionsOf (allowedFor count component) count value items)
      (restrictionsOf (allowedFor count' (rename relabel component)) count' (fun item => rename relabel (value item))
        items) where
  nodup := restrictionsOf_nodup _ _ _ _
  nodup' := restrictionsOf_nodup _ _ _ _
  inside := fun _ member => restrictionsOf_lt member
  inside' := fun _ member => restrictionsOf_lt member
  mem_iff := fun _ => preserving.mem_restrictions_rename

/-- **The renamed group's copy** is the original copy with its free names renamed and its restrictions reordered. -/
theorem copyOf_rename {count count' : Nat} {relabel : Nat → Nat} {restrictions restrictions' : List Nat}
    (image : ImageOf count count' relabel restrictions restrictions') (preserving : Preserving count count' relabel)
    (components : List Pattern) :
    copyOf block.toBlock count' ⟨restrictions', components.map (rename relabel)⟩ =
      Prenex.toPattern block.toBlock ⟨restrictions.length,
        ((components.map (rename (Prenex.permute count (splitOrder count (outsideOf count restrictions)
          restrictions)))).map (rename (liftIndex restrictions.length
            (copyRelabel count count' relabel restrictions restrictions')))).map
          (rename (Prenex.permute restrictions.length (copyOrder relabel restrictions restrictions')))⟩ := by
  unfold copyOf
  simp only [List.map_map]
  rw [image.length_eq preserving]
  congr 2
  apply List.map_congr_left
  intro component _
  simp only [Function.comp_apply, rename_comp]
  congr 1
  funext index
  exact image.split_comp preserving index

/-! ## The copy test of the renamed block -/

/-- **The canonical form below a size**, as absorption reads it: similar blocks have one canonical form, injective
renamings keep and reflect equalities of canonical forms, and keep whether a canonical form is a replication and
its size. -/
structure Below (block : ReplicationBlock) (bound : Nat) : Prop where
  similar : ∀ first second : Prenex, first.mass < bound → second.mass < bound → first.Atomic block.toBlock →
    second.Atomic block.toBlock → SimilarR block first second → normal block first = normal block second
  renamed : ∀ first second : Pattern, size first < bound → size second < bound → ∀ outer, Function.Injective outer →
    (canonicalOf block (rename outer first) = canonicalOf block (rename outer second) ↔
      canonicalOf block first = canonicalOf block second)
  shape : ∀ pattern, size pattern < bound → ∀ outer, Function.Injective outer →
    isReplicated block (canonicalOf block (rename outer pattern)) = isReplicated block (canonicalOf block pattern)
  sized : ∀ pattern, size pattern < bound → ∀ outer, Function.Injective outer →
    size (canonicalOf block (rename outer pattern)) = size (canonicalOf block pattern)

/-- The components at distinct places of a block weigh no more than all its components. -/
theorem sizeList_places_le {components : List Pattern} {items : List Nat} (nodup : items.Nodup)
    (inRange : ∀ member ∈ items, member < components.length) :
    sizeList (items.map (placeValue block components)) ≤ sizeList components := by
  have subperm : items.Subperm (List.range components.length) :=
    nodup.subperm fun member inItems => List.mem_range.mpr (inRange member inItems)
  have mapped : (items.map (placeValue block components)).Subperm
      ((List.range components.length).map (placeValue block components)) := by
    obtain ⟨middle, permutation, sublist⟩ := subperm
    exact ⟨middle.map _, permutation.map _, sublist.map _⟩
  have whole : (List.range components.length).map (placeValue block components) = components := by
    have := places_map (block := block) ⟨0, components⟩
    simpa [places] using congrArg Prenex.components this
  rw [whole] at mapped
  exact sizeList_subperm mapped

/-- A group's copy, as a block. -/
def copyBlock (count : Nat) (restrictions : List Nat) (components : List Pattern) : Prenex :=
  ⟨restrictions.length, components.map (rename (Prenex.permute count (splitOrder count (outsideOf count restrictions)
    restrictions)))⟩

/-- **A group's copy uses every restriction it binds.** -/
theorem copyBlock_used {allowed : List Nat} {count : Nat} {value : Nat → Pattern} {items : List Nat} :
    (copyBlock count (restrictionsOf allowed count value items) (items.map value)).Used := by
  intro position below
  simp only [copyBlock] at below ⊢
  set restrictions := restrictionsOf allowed count value items
  have member : restrictions[position] ∈ restrictions := List.getElem_mem below
  obtain ⟨item, inItems, keyed⟩ := mem_restrictionsOf.mp member
  unfold throughKeys at keyed
  obtain ⟨used, -⟩ := List.mem_filter.mp keyed
  obtain ⟨inside, mentioned⟩ := mem_usedRestrictions.mp used
  refine ⟨rename _ (value item), List.mem_map_of_mem (List.mem_map_of_mem inItems), ?_⟩
  rw [mentions_iff, freeIn_rename]
  refine ⟨restrictions[position], (mentions_iff _ _).mp mentioned, ?_⟩
  rw [permute_split_inside member inside, (restrictionsOf_nodup _ _ _ _).idxOf_getElem _ below]

/-- The weight of a group's copy: the block's restrictions and the group's components. -/
theorem copyBlock_mass {allowed : List Nat} {count : Nat} {value : Nat → Pattern} {items : List Nat} :
    (copyBlock count (restrictionsOf allowed count value items) (items.map value)).mass ≤
      2 * count + sizeList (items.map value) := by
  simp only [copyBlock, Prenex.mass, sizeList_map_rename]
  have := length_le_of_inside (restrictionsOf_nodup allowed count value items) fun _ member => restrictionsOf_lt member
  omega

theorem copyOf_eq_copyBlock (count : Nat) (group : Group) :
    copyOf block.toBlock count group = Prenex.toPattern block.toBlock (copyBlock count group.restrictions group.components) :=
  rfl

variable {count count' : Nat} {relabel : Nat → Nat}

/-- **The renamed group's copy reads canonically as the original copy, its free names renamed.** -/
theorem canonicalOf_copyOf_rename (preserving : Preserving count count' relabel) {bound : Nat}
    (below : Below block bound) {value : Nat → Pattern} {component : Pattern} {items : List Nat}
    (atomic : ∀ item ∈ items, decompose block.toBlock (value item) = Prenex.atom (value item))
    (small : 2 * count + sizeList (items.map value) < bound) :
    canonicalOf block (copyOf block.toBlock count' (asGroup (allowedFor count' (rename relabel component)) count'
        (fun item => rename relabel (value item)) items)) =
      canonicalOf block (rename (copyRelabel count count' relabel
          (restrictionsOf (allowedFor count component) count value items)
          (restrictionsOf (allowedFor count' (rename relabel component)) count' (fun item => rename relabel (value item))
            items))
        (copyOf block.toBlock count (asGroup (allowedFor count component) count value items))) := by
  set restrictions := restrictionsOf (allowedFor count component) count value items
  set restrictions' := restrictionsOf (allowedFor count' (rename relabel component)) count'
    (fun item => rename relabel (value item)) items
  have image : ImageOf count count' relabel restrictions restrictions' := imageOf_rename preserving value component items
  set copyRelabel' := copyRelabel count count' relabel restrictions restrictions'
  set order := copyOrder relabel restrictions restrictions'
  have isOrder := image.copyOrder_isOrder preserving
  have groupAtoms : ∀ member ∈ items.map value, decompose block.toBlock member = Prenex.atom member := by
    intro member inMembers
    obtain ⟨item, inItems, rfl⟩ := List.mem_map.mp inMembers
    exact atomic item inItems
  -- the original copy, as a block, renamed outside
  set original := copyBlock count restrictions (items.map value) with originalIs
  have originalAtomic : original.Atomic block.toBlock := atomic_map_rename groupAtoms _
  have originalUsed : original.Used := copyBlock_used
  set renamed := original.renameOuter copyRelabel' with renamedIs
  have renamedAtomic : renamed.Atomic block.toBlock := atomic_map_rename originalAtomic _
  have renamedUsed : renamed.Used := used_rename originalUsed fun index below => if_pos below
  set reordered : Prenex := ⟨restrictions.length, renamed.components.map (rename (Prenex.permute restrictions.length
    order))⟩ with reorderedIs
  have reorderedAtomic : reordered.Atomic block.toBlock := atomic_map_rename renamedAtomic _
  have reorderedUsed : reordered.Used := used_permute renamedUsed isOrder
  have masses : renamed.mass < bound ∧ reordered.mass < bound := by
    have originalMass : original.mass ≤ 2 * count + sizeList (items.map value) := copyBlock_mass
    have renamedMass : renamed.mass = original.mass := by
      rw [renamedIs]
      simp only [Prenex.renameOuter, Prenex.mass, sizeList_map_rename]
    have reorderedMass : reordered.mass = renamed.mass := by
      rw [reorderedIs]
      simp only [Prenex.mass, sizeList_map_rename]
      rw [renamedIs]
      rfl
    exact ⟨by omega, by omega⟩
  have copyIs : copyOf block.toBlock count' (asGroup (allowedFor count' (rename relabel component)) count'
      (fun item => rename relabel (value item)) items) = Prenex.toPattern block.toBlock reordered := by
    have mapped : items.map (fun item => rename relabel (value item)) = (items.map value).map (rename relabel) := by
      rw [List.map_map]
      rfl
    unfold asGroup
    rw [mapped, copyOf_rename image preserving]
    rfl
  unfold canonicalOf
  rw [copyIs, decompose_toPattern reorderedAtomic reorderedUsed, copyOf_eq_copyBlock, decompose_renameOuter]
  simp only [asGroup]
  rw [decompose_toPattern originalAtomic originalUsed]
  congr 1
  exact (below.similar renamed reordered masses.1 masses.2 renamedAtomic reorderedAtomic
    ⟨rfl, order, reordered.components, isOrder, List.forall₂_same.mpr fun component _ => AlikeR.refl component,
      List.Perm.refl _⟩).symm

theorem size_argumentOf?_le (component : Pattern) : size (argumentOf? component) ≤ size component := by
  match component with
  | .apply _ [argument] => simp [argumentOf?, size, sizeList]
  | .apply _ [] => simp [argumentOf?]
  | .apply _ (_ :: _ :: _) => simp [argumentOf?]
  | .bvar _ => simp [argumentOf?]
  | .fvar _ => simp [argumentOf?]
  | .lambda _ _ => simp [argumentOf?]
  | .multiLambda _ _ _ => simp [argumentOf?]
  | .subst _ _ => simp [argumentOf?]
  | .collection _ _ _ => simp [argumentOf?]

theorem placeValue_mem {components : List Pattern} {place : Nat} (inside : place < components.length) :
    placeValue block components place ∈ components := by
  unfold placeValue
  rw [List.getD_eq_getElem _ _ inside]
  exact List.getElem_mem inside

/-- **The renamed block tests copies as the original does.** -/
theorem copyTest_rename (preserving : Preserving count count' relabel) {components : List Pattern}
    (below : Below block (Prenex.mass ⟨count, components⟩))
    (atomic : ∀ component ∈ components, decompose block.toBlock component = Prenex.atom component)
    {place : Nat} {items : List Nat} (nodup : (place :: items).Nodup)
    (inRange : ∀ member ∈ place :: items, member < components.length)
    (replicated : isReplicated block (placeValue block components place) = true) :
    CopyTest block (canonicalOf block) count' (placeValue block (components.map (rename relabel)) place)
        (asGroup (allowedFor count' (placeValue block (components.map (rename relabel)) place)) count'
          (placeValue block (components.map (rename relabel))) items) ↔
      CopyTest block (canonicalOf block) count (placeValue block components place)
        (asGroup (allowedFor count (placeValue block components place)) count (placeValue block components) items) := by
  have valueRenamed : placeValue block (components.map (rename relabel)) =
      fun item => rename relabel (placeValue block components item) :=
    funext (placeValue_map_rename relabel components)
  have itemsAtomic : ∀ item ∈ items, decompose block.toBlock (placeValue block components item) =
      Prenex.atom (placeValue block components item) := fun item inItems =>
    atomic _ (placeValue_mem (inRange item (List.mem_cons_of_mem _ inItems)))
  rw [valueRenamed]
  set value := placeValue block components with valueIs
  obtain ⟨argument, componentIs⟩ := replicated_shape replicated
  -- what the group weighs
  have weights : sizeList ((place :: items).map value) ≤ sizeList components := sizeList_places_le nodup inRange
  simp only [List.map_cons, sizeList] at weights
  have componentSize : size (value place) = size argument + 1 := by
    rw [componentIs]
    simp [size, sizeList]
  have argumentPositive := size_pos argument
  have itemsSmall : 2 * count + sizeList (items.map value) < Prenex.mass ⟨count, components⟩ := by
    simp only [Prenex.mass]
    omega
  have argumentSmall : size argument < Prenex.mass ⟨count, components⟩ := by
    simp only [Prenex.mass]
    omega
  have copyCanonical := canonicalOf_copyOf_rename preserving below (component := value place) itemsAtomic itemsSmall
  set restrictions := restrictionsOf (allowedFor count (value place)) count value items with restrictionsIs
  set restrictions' := restrictionsOf (allowedFor count' (rename relabel (value place))) count'
    (fun item => rename relabel (value item)) items with restrictions'Is
  have image : ImageOf count count' relabel restrictions restrictions' :=
    imageOf_rename preserving value (value place) items
  have injective := image.copyRelabel_injective preserving
  have copySmall : size (copyOf block.toBlock count (asGroup (allowedFor count (value place)) count value items)) <
      Prenex.mass ⟨count, components⟩ := by
    rw [copyOf_eq_copyBlock]
    have toPatternSize := size_toPattern_le (block := block.toBlock)
      (copyBlock count (asGroup (allowedFor count (value place)) count value items).restrictions
        (asGroup (allowedFor count (value place)) count value items).components)
    have massSmall := copyBlock_mass (allowed := allowedFor count (value place)) (count := count) (value := value)
      (items := items)
    simp only [asGroup] at toPatternSize ⊢
    simp only [Prenex.mass] at itemsSmall ⊢
    omega
  have targetIs : rename (Prenex.groupIndex count' (outsideOf count' restrictions'))
        (argumentOf? (rename relabel (value place))) =
      rename (copyRelabel count count' relabel restrictions restrictions')
        (rename (Prenex.groupIndex count (outsideOf count restrictions)) (argumentOf? (value place))) := by
    rw [argumentOf?_rename, componentIs]
    simp only [argumentOf?]
    rw [rename_comp, rename_comp]
    apply rename_congr
    intro index free
    refine image.groupIndex_comp preserving fun _ member => ?_
    have allowed := restrictionsOf_allowed member
    simp only [allowedFor, List.mem_filter, List.mem_range, Bool.not_eq_true'] at allowed
    have mentioned : mentions index (value place) = true := by
      rw [componentIs, mentions_iff]
      exact (mentions_iff _ _).mp ((mentions_iff _ _).mpr (Mettapedia.OSLF.MeTTaIL.CanonicalBags.freeIn_apply.mpr
        ⟨argument, List.mem_singleton_self _, free⟩))
    rw [mentioned] at allowed
    cases allowed.2
  have targetSmall : size (rename (Prenex.groupIndex count (outsideOf count restrictions)) (argumentOf? (value place))) <
      Prenex.mass ⟨count, components⟩ := by
    rw [size_rename, componentIs]
    simpa [argumentOf?] using argumentSmall
  unfold CopyTest
  simp only [asGroup] at copyCanonical ⊢
  refine and_congr ?_ (and_congr ?_ (and_congr ?_ ?_))
  · rw [copyCanonical, targetIs]
    simp only [asGroup] at copySmall
    exact below.renamed _ _ copySmall targetSmall _ injective
  · rw [copyCanonical]
    simp only [asGroup] at copySmall
    rw [below.shape _ copySmall _ injective]
  · rw [List.forall_mem_map, List.forall_mem_map]
    refine forall_congr' fun item => forall_congr' fun inItems => ?_
    have itemSmall : size (argumentOf? (value item)) < Prenex.mass ⟨count, components⟩ := by
      have := size_argumentOf?_le (value item)
      have := size_lt_of_mem (List.mem_map_of_mem (f := value) inItems)
      simp only [Prenex.mass] at itemsSmall ⊢
      omega
    have placeSmall : size (argumentOf? (value place)) < Prenex.mass ⟨count, components⟩ := by
      rw [componentIs]
      simpa [argumentOf?] using argumentSmall
    rw [isReplicated_rename, argumentOf?_rename, argumentOf?_rename, below.sized _ itemSmall _ preserving.injective,
      below.sized _ placeSmall _ preserving.injective]
  · constructor
    · intro renamedMentions index inside mentioned
      obtain ⟨member, inMap, mentionedMember⟩ := renamedMentions (relabel index) (preserving.below index inside)
        (by rw [mentions_rename_injective preserving.injective]; exact mentioned)
      obtain ⟨item, inItems, rfl⟩ := List.mem_map.mp inMap
      exact ⟨value item, List.mem_map_of_mem inItems, by
        rwa [mentions_rename_injective preserving.injective] at mentionedMember⟩
    · intro originalMentions index' inside' mentioned'
      obtain ⟨index, rfl, mentioned⟩ := mentions_rename_image _ mentioned'
      obtain ⟨member, inMap, mentionedMember⟩ := originalMentions index (preserving.lt_iff.mp inside') mentioned
      obtain ⟨item, inItems, rfl⟩ := List.mem_map.mp inMap
      exact ⟨rename relabel (value item), List.mem_map_of_mem (f := fun item => rename relabel (value item)) inItems,
        by rw [mentions_rename_injective preserving.injective]; exact mentionedMember⟩

/-- **The renamed block's system is the original's**, its restrictions relabelled. -/
theorem rename_iso (preserving : Preserving count count' relabel) {components : List Pattern}
    (below : Below block (Prenex.mass ⟨count, components⟩))
    (atomic : ∀ component ∈ components, decompose block.toBlock component = Prenex.atom component) :
    (blockSystem block ⟨count, components⟩).Iso (blockSystem block ⟨count', components.map (rename relabel)⟩)
      (places ⟨count, components⟩).toFinset id relabel where
  injective := fun _ _ _ _ same => same
  relabelInjective := preserving.injective
  mentions := fun place _ => by
    ext index'
    simp only [blockSystem, absorptionSystem, id, List.mem_toFinset, Finset.mem_image, mem_usedRestrictions]
    rw [placeValue_map_rename]
    constructor
    · rintro ⟨inside', mentioned'⟩
      obtain ⟨index, rfl, mentioned⟩ := mentions_rename_image _ mentioned'
      exact ⟨index, ⟨preserving.lt_iff.mp inside', mentioned⟩, rfl⟩
    · rintro ⟨index, ⟨inside, mentioned⟩, rfl⟩
      exact ⟨preserving.below index inside, by rw [mentions_rename_injective preserving.injective]; exact mentioned⟩
  replicated := fun place _ => by
    simp only [blockSystem, absorptionSystem, id]
    rw [placeValue_map_rename, isReplicated_rename]
  copy := fun group inside place placeLive replicated notIn => by
    simp only [blockSystem, absorptionSystem, Finset.image_id, id]
    have placeRange := List.mem_range.mp (List.mem_toFinset.mp placeLive)
    exact copyTest_rename preserving below atomic
      (List.nodup_cons.mpr ⟨fun inSorted => notIn ((Finset.mem_sort _).mp inSorted), Finset.sort_nodup _ _⟩)
      (fun member inList => by
        rcases List.mem_cons.mp inList with rfl | inSorted
        · exact placeRange
        · exact List.mem_range.mp (List.mem_toFinset.mp (inside ((Finset.mem_sort _).mp inSorted))))
      replicated
  height := fun place placeLive replicated => by
    simp only [blockSystem, absorptionSystem, id] at replicated ⊢
    obtain ⟨argument, componentIs⟩ := replicated_shape replicated
    have placeRange := List.mem_range.mp (List.mem_toFinset.mp placeLive)
    have componentSmall := size_lt_of_mem (placeValue_mem (block := block) placeRange)
    rw [placeValue_map_rename, argumentOf?_rename]
    refine below.sized _ ?_ _ preserving.injective
    rw [componentIs] at componentSmall ⊢
    simp only [argumentOf?, size, sizeList, Prenex.mass] at componentSmall ⊢
    omega

end Mettapedia.GSLT.LanguageDef.RestrictionBlocks




