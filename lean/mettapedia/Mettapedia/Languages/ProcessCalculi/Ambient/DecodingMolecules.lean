import Mettapedia.Languages.ProcessCalculi.Ambient.DecodingCanonical

/-!
# Reading back molecules

A block whose components fall into parts using disjoint sets of its restrictions reads back as its parts side by side
(`decode_split`), each a block over the restrictions it uses; so a block reads back as its molecules side by side
(`decode_partition`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.Ambient.Decoding

open Mettapedia.Languages.ProcessCalculi.Ambient.Comm (ambientCoreCalc)

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Substitution (liftBVars)
open Mettapedia.OSLF.MeTTaIL.CanonicalBags (FreeIn)
open Mettapedia.GSLT.LanguageDef.WellSorted (HasType FreeTypeContext)
open Mettapedia.GSLT.LanguageDef.RestrictionBlocks (Prenex Members ProcEquiv rename rename_congr SplitParts splitOrder
  splitPlace splitOrder_getD unusedRestrictions lowerAbove first_part_renaming second_part_renaming par_equivalent
  outsideOf mem_outsideOf IsOrder)
open Mettapedia.Languages.ProcessCalculi.Ambient.Full (ambientBlock)
open Mettapedia.Languages.ProcessCalculi.Ambient.Located (locatedCalc locatedBlock locatedRepBlock)
open Mettapedia.Languages.ProcessCalculi.Ambient.Encoding (nameType procType)

variable {free : FreeTypeContext}

/-- **A part of a well-located block, over the restrictions it uses, is well-located**, when the other components use
none of those. -/
theorem WellLocated.part {isLoc : Pattern → Prop} {place : Pattern} {count : Nat} {first : List Nat}
    {partOne partTwo : List Pattern}
    (well : WellLocated isLoc place ⟨count, partOne ++ partTwo⟩) (locVariables : LocVariables isLoc)
    (nodup : first.Nodup) (inside : ∀ index ∈ first, index < count)
    (oneUses : ∀ component ∈ partOne, ∀ index, FreeIn index component → index < count → index ∈ first)
    (twoApart : ∀ component ∈ partTwo, ∀ index ∈ first, ¬ FreeIn index component) :
    WellLocated isLoc place ⟨first.length, partOne.map (rename (Prenex.groupIndex count first))⟩ := by
  have oneWell : WellLocated isLoc place ⟨count, partOne⟩ := by
    refine well.drop locVariables (dropped := partTwo) List.perm_append_comm
      fun component member index isPlaced marker inTwo isChild => ?_
    obtain ⟨child, below, same⟩ := childOf_bvar_of_kind
      (well.kinds marker (List.mem_append_right _ inTwo)) isChild
    simp only [Pattern.bvar.injEq] at same
    subst same
    change index < count at below
    exact twoApart marker inTwo index (oneUses component member index (freeIn_placeAt isPlaced) below)
      (freeIn_child isChild)
  refine WellLocated.comap (relabel := ungroup count first) (ungroup_injective nodup inside)
    (fun index below => by
      simp only [ungroup, below, if_true]
      rw [List.getD_eq_getElem _ _ below]
      exact inside _ (List.getElem_mem below))
    (fun offset => by simp only [ungroup]; split_ifs <;> omega) ?_ locVariables
  rw [ungroup_restores inside oneUses]
  exact oneWell

theorem filter_range_lt {kept : Nat} : ∀ {count : Nat}, kept ≤ count →
    (List.range count).filter (fun index => decide (index < kept)) = List.range kept
  | 0, below => by
      have : kept = 0 := by omega
      subst this
      rfl
  | count + 1, below => by
      rw [List.range_succ, List.filter_append]
      by_cases equal : kept = count + 1
      · subst equal
        rw [List.filter_eq_self.mpr fun index member => by simpa using Nat.lt_succ_of_lt (List.mem_range.mp member)]
        simp [List.range_succ]
      · rw [filter_range_lt (by omega)]
        simp [show ¬ count < kept by omega]

theorem idxOf_range {kept index : Nat} (below : index < kept) : (List.range kept).idxOf index = index := by
  have member : index ∈ List.range kept := List.mem_range.mpr below
  have nodup : (List.range kept).Nodup := List.nodup_range
  have get := List.getElem_idxOf (List.idxOf_lt_length_of_mem member)
  rw [List.getElem_range] at get
  exact get

/-- **A block whose components fall into two parts using disjoint restrictions reads back as the parts side by
side**, each over the restrictions it uses. -/
theorem decode_split {bound : List TypeExpr} {isLoc : Pattern → Prop} {outer count : Nat} {first second : List Nat}
    (parts : SplitParts count first second) {partOne partTwo : List Pattern}
    (well : WellLocated isLoc (.bvar outer) ⟨count, partOne ++ partTwo⟩) (locVariables : LocVariables isLoc)
    (members : Members locatedCalc locatedBlock free (List.replicate count nameType ++ bound) (partOne ++ partTwo))
    (oneUses : ∀ component ∈ partOne, ∀ index, FreeIn index component → index < count → index ∈ first)
    (twoUses : ∀ component ∈ partTwo, ∀ index, FreeIn index component → index < count → index ∈ second)
    (fuel : Nat) :
    ProcEquiv ambientCoreCalc ambientBlock free bound
      (Prenex.toPattern ambientBlock (decodeForm (fuel + 1) (.bvar outer) ⟨count, partOne ++ partTwo⟩))
      (.collection .hashBag
        [Prenex.toPattern ambientBlock (decodeForm (fuel + 1) (.bvar outer)
          ⟨first.length, partOne.map (rename (Prenex.groupIndex count first))⟩),
         Prenex.toPattern ambientBlock (decodeForm (fuel + 1) (.bvar outer)
          ⟨second.length, partTwo.map (rename (Prenex.groupIndex count second))⟩)] none) := by
  have signature : Mettapedia.GSLT.LanguageDef.RestrictionBlocks.BlockSignature locatedCalc locatedBlock :=
    Mettapedia.Languages.ProcessCalculi.Ambient.Located.locatedLanguage.toBlockSignature
  set order := splitOrder count first second with orderIs
  have isOrder : IsOrder count order := parts.splitOrder_perm
  have total := parts.lengths
  set kept := second.length + first.length with keptIs
  set unusedHere := (List.range count).filter fun index => decide (kept ≤ index) with unusedHereIs
  have unusedNodup : unusedHere.Nodup := List.nodup_range.filter _
  have unusedInside : ∀ index ∈ unusedHere, index < count :=
    fun index member => List.mem_range.mp (List.mem_filter.mp member).1
  -- the reordered components use only the kept restrictions
  have uses : ∀ component ∈ (partOne ++ partTwo).map (rename (Prenex.permute count order)),
      ∀ index, FreeIn index component → index < count → index < kept := by
    intro component member index freeHere low
    obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp member
    obtain ⟨source, sourceFree, moved⟩ := (Mettapedia.GSLT.LanguageDef.RestrictionBlocks.freeIn_rename original).mp
      freeHere
    simp only [Prenex.permute] at moved
    split_ifs at moved with sourceInside
    · rw [orderIs, splitOrder_getD sourceInside] at moved
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
  have apart : ∀ component ∈ (partOne ++ partTwo).map (rename (Prenex.permute count order)),
      ∀ index ∈ unusedHere, ¬ FreeIn index component := by
    intro component member index listed freeHere
    obtain ⟨inRange, high⟩ := List.mem_filter.mp listed
    simp only [decide_eq_true_eq] at high
    have := uses component member index freeHere (List.mem_range.mp inRange)
    omega
  have outsideIs : outsideOf count unusedHere = List.range kept := by
    unfold outsideOf
    rw [← filter_range_lt (kept := kept) (count := count) (by omega)]
    apply List.filter_congr
    intro index member
    have below := List.mem_range.mp member
    by_cases low : index < kept
    · have notListed : index ∉ unusedHere := fun listed => by
        have high := (List.mem_filter.mp listed).2
        simp only [decide_eq_true_eq] at high
        omega
      simp [notListed, low]
    · have listed : index ∈ unusedHere := List.mem_filter.mpr ⟨member, by simp only [decide_eq_true_eq]; omega⟩
      simp [listed, low]
  obtain ⟨reorderedMembers, -⟩ := Mettapedia.GSLT.LanguageDef.RestrictionBlocks.block_reorder_equivalent
    (language := locatedCalc) (block := locatedBlock) (bound := bound)
    (Mettapedia.GSLT.LanguageDef.RestrictionBlocks.orders_reorders (List.range count) order
      (Mettapedia.GSLT.LanguageDef.RestrictionBlocks.orders_complete _ _ isOrder)) members
  have reordered := decode_reorder (free := free) fuel (.bvar outer) isOrder members
  have dropped := decode_drop (free := free) fuel (.bvar outer) unusedNodup unusedInside reorderedMembers apart
  rw [outsideIs, List.length_range] at dropped
  -- the narrowed block is the two parts side by side
  have components : ((partOne ++ partTwo).map (rename (Prenex.permute count order))).map
      (rename (Prenex.groupIndex count (List.range kept))) =
      (Prenex.par ⟨first.length, partOne.map (rename (Prenex.groupIndex count first))⟩
        ⟨second.length, partTwo.map (rename (Prenex.groupIndex count second))⟩).components := by
    have lowered : ∀ component ∈ (partOne ++ partTwo).map (rename (Prenex.permute count order)),
        rename (Prenex.groupIndex count (List.range kept)) component =
          rename (lowerAbove kept (unusedRestrictions count first second).length) component := by
      intro component member
      apply rename_congr
      intro index freeHere
      simp only [Prenex.groupIndex, lowerAbove]
      by_cases below : index < count
      · have low := uses component member index freeHere below
        simp only [below, if_true, low, idxOf_range low]
      · simp only [below, if_false, List.length_range, show ¬ index < kept by omega]
        omega
    rw [List.map_congr_left lowered]
    simp only [Prenex.par, List.map_append, List.map_map]
    congr 1
    · apply List.map_congr_left
      intro component member
      exact first_part_renaming parts (oneUses component member)
    · apply List.map_congr_left
      intro component member
      exact second_part_renaming parts (twoUses component member)
  have parCount : kept = (Prenex.par ⟨first.length, partOne.map (rename (Prenex.groupIndex count first))⟩
      ⟨second.length, partTwo.map (rename (Prenex.groupIndex count second))⟩).count := by
    simp only [Prenex.par, keptIs]
    omega
  rw [components, parCount] at dropped
  -- the parts are well-located, so they read back side by side
  have oneWell := well.part locVariables parts.firstNodup parts.firstInside oneUses
    fun component member index listed freeHere =>
      parts.disjoint index listed (twoUses component member index freeHere (parts.firstInside index listed))
  have twoWell := (well.drop locVariables (dropped := []) List.perm_append_comm (by simp)).part locVariables
    parts.secondNodup parts.secondInside twoUses
    fun component member index listed freeHere =>
      parts.disjoint index (oneUses component member index freeHere (parts.secondInside index listed)) listed
  have sideBySide := decodeForm_par fuel (.bvar outer) oneWell.rooted twoWell.rooted
  have oneMembers := Mettapedia.GSLT.LanguageDef.RestrictionBlocks.part_members (language := locatedCalc)
    (block := locatedBlock) (restrictions := first)
    (fun element member => members element (List.mem_append_left _ member)) oneUses
  have twoMembers := Mettapedia.GSLT.LanguageDef.RestrictionBlocks.part_members (language := locatedCalc)
    (block := locatedBlock) (restrictions := second)
    (fun element member => members element (List.mem_append_right _ member)) twoUses
  have decodedOne := (decode_typed (free := free) (fuel + 1)).1 (.bvar outer)
    ⟨first.length, partOne.map (rename (Prenex.groupIndex count first))⟩ oneMembers
  have decodedTwo := (decode_typed (free := free) (fuel + 1)).1 (.bvar outer)
    ⟨second.length, partTwo.map (rename (Prenex.groupIndex count second))⟩ twoMembers
  have paired := par_equivalent (language := ambientCoreCalc) (block := ambientBlock) decodedOne decodedTwo
  rw [← sideBySide] at paired
  exact .trans _ _ _ (Relation.EqvGen.symm _ _ reordered) (.trans _ _ _ (Relation.EqvGen.symm _ _ dropped)
    (Relation.EqvGen.symm _ _ paired))

/-! ## Molecules -/

open Mettapedia.GSLT.LanguageDef.RestrictionBlocks (Group Partition molecule_relabel bag_cons_equivalent bag_fill
  restricts_unit_equivalent part_members bag_body_equivalent)
open Mettapedia.Languages.ProcessCalculi.Ambient.Full (ambientRepBlock)

/-- **A block reads back as its parts side by side**, each a molecule over its own restrictions. -/
theorem decode_partition {bound : List TypeExpr} {isLoc : Pattern → Prop} {outer : Nat}
    (locVariables : LocVariables isLoc) (fuel : Nat) :
    ∀ {count : Nat} {parts : List Group}, Partition count parts →
      WellLocated isLoc (.bvar outer) ⟨count, parts.flatMap Group.components⟩ →
      Members locatedCalc locatedBlock free (List.replicate count nameType ++ bound) (parts.flatMap Group.components) →
      ProcEquiv ambientCoreCalc ambientBlock free bound
        (Prenex.toPattern ambientBlock (decodeForm (fuel + 1) (.bvar outer) ⟨count, parts.flatMap Group.components⟩))
        (.collection .hashBag (parts.map fun group =>
          Prenex.toPattern ambientBlock (decodeForm (fuel + 1) (.bvar outer) (Prenex.molecule count group))) none)
  | count, [], _, _, _ => by
      simp only [List.flatMap_nil, List.map_nil]
      have empty : readPlaced fuel (liftBVars 0 count (.bvar outer)) [] = [] := by cases fuel <;> rfl
      simp only [decodeForm, Prenex.toPattern, empty]
      exact .trans _ _ _ (restricts_unit_equivalent (language := ambientCoreCalc) (block := ambientRepBlock) count)
        (Relation.EqvGen.symm _ _ (bag_body_equivalent (language := ambientCoreCalc) (block := ambientBlock)
          Members.nil))
  | count, group :: rest, partition, well, members => by
      have parts := partition.splitParts
      have restPartition := partition.tail
      simp only [List.flatMap_cons] at well members ⊢
      have oneMembers : Members locatedCalc locatedBlock free (List.replicate count nameType ++ bound)
          group.components := fun element member => members element (List.mem_append_left _ member)
      have twoMembers : Members locatedCalc locatedBlock free (List.replicate count nameType ++ bound)
          (rest.flatMap Group.components) := fun element member => members element (List.mem_append_right _ member)
      have split := decode_split (free := free) parts well locVariables members
        (partition.uses group List.mem_cons_self) restPartition.rest_uses fuel
      have relabelledMembers := part_members (language := locatedCalc) (block := locatedBlock)
        (restrictions := Partition.outer rest) twoMembers restPartition.rest_uses
      have components : (rest.flatMap Group.components).map
          (rename (Prenex.groupIndex count (Partition.outer rest))) =
          (rest.map (Group.relabel count (Partition.outer rest))).flatMap Group.components := by
        simp [Group.relabel, List.map_flatMap, List.flatMap_map]
      have restWell : WellLocated isLoc (.bvar outer) ⟨(Partition.outer rest).length,
          (rest.map (Group.relabel count (Partition.outer rest))).flatMap Group.components⟩ := by
        rw [← components]
        exact (well.drop locVariables (dropped := []) List.perm_append_comm (by simp)).part locVariables
          parts.secondNodup parts.secondInside restPartition.rest_uses
          fun component member index listed freeHere =>
            parts.disjoint index (partition.uses group List.mem_cons_self component member index freeHere
              (parts.secondInside index listed)) listed
      rw [components] at split relabelledMembers
      have inner := decode_partition locVariables fuel restPartition.relabel restWell relabelledMembers
      have molecules : (rest.map (Group.relabel count (Partition.outer rest))).map
          (fun other => Prenex.toPattern ambientBlock
            (decodeForm (fuel + 1) (.bvar outer) (Prenex.molecule (Partition.outer rest).length other))) =
          rest.map fun other => Prenex.toPattern ambientBlock
            (decodeForm (fuel + 1) (.bvar outer) (Prenex.molecule count other)) := by
        rw [List.map_map]
        apply List.map_congr_left
        intro other member
        simp only [Function.comp_apply]
        rw [molecule_relabel (fun index listed => List.mem_flatMap.mpr ⟨other, member, listed⟩)
          (restPartition.uses other member)]
      rw [molecules] at inner
      have groupTyped := (decode_typed (free := free) (fuel + 1)).1 (.bvar outer) (Prenex.molecule count group)
        (part_members (language := locatedCalc) (block := locatedBlock) oneMembers
          (partition.uses group List.mem_cons_self))
      have moleculeMembers : Members ambientCoreCalc ambientBlock free bound (rest.map fun other =>
          Prenex.toPattern ambientBlock (decodeForm (fuel + 1) (.bvar outer) (Prenex.molecule count other))) := by
        intro element member
        obtain ⟨other, otherMember, rfl⟩ := List.mem_map.mp member
        exact decodeForm_typed (fuel + 1) (.bvar outer) (part_members (language := locatedCalc)
          (block := locatedBlock) (fun element listed => twoMembers element
            (List.mem_flatMap.mpr ⟨other, otherMember, listed⟩)) (restPartition.uses other otherMember))
      have groupPattern := Mettapedia.GSLT.LanguageDef.RestrictionBlocks.restricts_typed (language := ambientCoreCalc)
        (block := ambientBlock) _ (Mettapedia.GSLT.LanguageDef.RestrictionBlocks.body_typed groupTyped)
      have filled := bag_fill (language := ambientCoreCalc) (block := ambientBlock)
        (before := [Prenex.toPattern ambientBlock (decodeForm (fuel + 1) (.bvar outer) (Prenex.molecule count group))])
        (after := []) (rest := none) (Members.cons groupPattern Members.nil) Members.nil inner
      simp only [List.cons_append, List.nil_append] at filled
      simp only [List.map_cons]
      exact .trans _ _ _ split (.trans _ _ _ filled (bag_cons_equivalent groupPattern moleculeMembers))
termination_by _ parts => parts.length
decreasing_by simp

/-- **The restrictions of a molecule are used by it**: the groups of a block are its groups through all its
restrictions, whose restrictions are those their components use. -/
theorem groups_covered (form : Prenex) : ∀ group ∈ Mettapedia.GSLT.LanguageDef.RestrictionBlocks.groups form,
    ∀ index ∈ group.restrictions, ∃ component ∈ group.components, FreeIn index component := by
  obtain ⟨count, components⟩ := form
  have asThrough : Mettapedia.GSLT.LanguageDef.RestrictionBlocks.groups ⟨count, components⟩ =
      Mettapedia.GSLT.LanguageDef.RestrictionBlocks.groupsThrough (List.range count) count components := by
    unfold Mettapedia.GSLT.LanguageDef.RestrictionBlocks.groups
      Mettapedia.GSLT.LanguageDef.RestrictionBlocks.groupsThrough
      Mettapedia.GSLT.LanguageDef.RestrictionBlocks.insertComponent
    congr 1
    funext groups component
    congr 1
    refine (List.filter_eq_self.mpr fun index member => ?_).symm
    have := (Mettapedia.GSLT.LanguageDef.RestrictionBlocks.mem_usedRestrictions.mp member).1
    simpa using this
  intro group groupMember index listed
  rw [asThrough] at groupMember
  have mapped := Mettapedia.GSLT.LanguageDef.RestrictionBlocks.groupsThrough_map (List.range count) count id components
  rw [List.map_id] at mapped
  rw [mapped] at groupMember
  obtain ⟨items, -, rfl⟩ := List.mem_map.mp groupMember
  obtain ⟨item, inItems, keyed⟩ := Mettapedia.GSLT.LanguageDef.RestrictionBlocks.mem_restrictionsOf.mp listed
  simp only [Mettapedia.GSLT.LanguageDef.RestrictionBlocks.throughKeys, List.mem_filter,
    Mettapedia.GSLT.LanguageDef.RestrictionBlocks.mem_usedRestrictions] at keyed
  exact ⟨item, by simpa [Mettapedia.GSLT.LanguageDef.RestrictionBlocks.asGroup] using inItems,
    (Mettapedia.GSLT.LanguageDef.RestrictionBlocks.mentions_iff item index).mp keyed.1.2⟩

/-- **A well-located block with a component has one at its place**: following the markers up from any component's
place, depths fall, so a marker at the place is reached. -/
theorem WellLocated.sits_at_place {isLoc : Pattern → Prop} {place : Pattern} {count : Nat} {components : List Pattern}
    (well : WellLocated isLoc place ⟨count, components⟩) {component : Pattern} (member : component ∈ components) :
    ∃ top ∈ components, placeAt top = some (liftBVars 0 count place) := by
  have hasPlace : ∀ other ∈ components, ∃ at', placeAt other = some at' := by
    intro other inComponents
    cases well.kinds other inComponents with
    | marker isMarker _ => exact ⟨_, placeAt_ofMarker isMarker _ _ _⟩
    | capability listed => exact ⟨_, placeAt_capability listed _ _ _⟩
    | replication => exact Option.isSome_iff_exists.mp (well.repsPlaced _ inComponents _ rfl)
    | cap => exact ⟨_, placeAt_cap _ _ _⟩
    | input listed => exact ⟨_, placeAt_input listed _ _⟩
    | output listed => exact ⟨_, placeAt_output listed _ _⟩
  obtain ⟨depth, grows⟩ := well.nested
  have climb : ∀ height, ∀ other ∈ components, ∀ index, placeAt other = some (.bvar index) → index < count →
      depth index = height → ∃ top ∈ components, placeAt top = some (liftBVars 0 count place) := by
    intro height
    induction height using Nat.strong_induction_on with
    | _ height recurse =>
        intro other inComponents index isPlaced below depthIs
        obtain ⟨marker, markerMember, isChild⟩ : Marked components index := by
          rcases well.placed other inComponents _ isPlaced with same | ⟨other', -, same, isMarked⟩
          · exact absurd same (by
              cases place with
              | bvar outer => simp [liftBVars]; omega
              | _ => simp [liftBVars])
          · simp only [Pattern.bvar.injEq] at same
            subst same
            exact isMarked
        obtain ⟨at', markerPlace⟩ := hasPlace marker markerMember
        rcases well.placed marker markerMember at' markerPlace with same | ⟨above, aboveBelow, rfl, -⟩
        · exact ⟨marker, markerMember, by rw [markerPlace, same]⟩
        · exact recurse (depth above) (by
              have := grows marker markerMember above index aboveBelow below markerPlace isChild
              omega) marker markerMember above markerPlace aboveBelow rfl
  obtain ⟨at', isPlaced⟩ := hasPlace component member
  rcases well.placed component member at' isPlaced with same | ⟨index, below, rfl, -⟩
  · exact ⟨component, member, by rw [isPlaced, same]⟩
  · exact climb _ component member index isPlaced below rfl

/-- **Every molecule of a block has a component.** -/
theorem groups_nonempty (form : Prenex) : ∀ group ∈ Mettapedia.GSLT.LanguageDef.RestrictionBlocks.groups form,
    group.components ≠ [] := by
  obtain ⟨count, components⟩ := form
  have asThrough : Mettapedia.GSLT.LanguageDef.RestrictionBlocks.groups ⟨count, components⟩ =
      Mettapedia.GSLT.LanguageDef.RestrictionBlocks.groupsThrough (List.range count) count components := by
    unfold Mettapedia.GSLT.LanguageDef.RestrictionBlocks.groups
      Mettapedia.GSLT.LanguageDef.RestrictionBlocks.groupsThrough
      Mettapedia.GSLT.LanguageDef.RestrictionBlocks.insertComponent
    congr 1
    funext groups component
    congr 1
    refine (List.filter_eq_self.mpr fun index member => ?_).symm
    have := (Mettapedia.GSLT.LanguageDef.RestrictionBlocks.mem_usedRestrictions.mp member).1
    simpa using this
  intro group groupMember
  rw [asThrough] at groupMember
  have mapped := Mettapedia.GSLT.LanguageDef.RestrictionBlocks.groupsThrough_map (List.range count) count id components
  rw [List.map_id] at mapped
  rw [mapped] at groupMember
  obtain ⟨items, inBuild, rfl⟩ := List.mem_map.mp groupMember
  have grouping := Mettapedia.GSLT.LanguageDef.RestrictionBlocks.Linked.build_grouping
    (keys := Mettapedia.GSLT.LanguageDef.RestrictionBlocks.throughKeys (List.range count) count id) components
  simpa [Mettapedia.GSLT.LanguageDef.RestrictionBlocks.asGroup] using grouping.nonempty items inBuild

/-- **A molecule of a well-located block**: well-located at the block's place, typed, its own block, with a component
at the place. -/
theorem molecule_facts {bound : List TypeExpr} {isLoc : Pattern → Prop} {outer count : Nat}
    {components : List Pattern}
    (well : WellLocated isLoc (.bvar outer) ⟨count, components⟩) (locVariables : LocVariables isLoc)
    (members : Members locatedCalc locatedBlock free (List.replicate count nameType ++ bound) components)
    {group : Group} (member : group ∈ Mettapedia.GSLT.LanguageDef.RestrictionBlocks.groups ⟨count, components⟩) :
    WellLocated isLoc (.bvar outer) (Prenex.molecule count group) ∧
      Members locatedCalc locatedBlock free (List.replicate (Prenex.molecule count group).count nameType ++ bound)
        (Prenex.molecule count group).components ∧
      Mettapedia.GSLT.LanguageDef.RestrictionBlocks.decompose locatedBlock
        (Prenex.toPattern locatedBlock (Prenex.molecule count group)) = Prenex.molecule count group ∧
      ∃ top ∈ (Prenex.molecule count group).components,
        placeAt top = some (.bvar (outer + (Prenex.molecule count group).count)) := by
  obtain ⟨partition, permuted⟩ := Mettapedia.GSLT.LanguageDef.RestrictionBlocks.groups_partition ⟨count, components⟩
  simp only at partition permuted
  obtain ⟨pre, post, splitIs⟩ := List.append_of_mem member
  have whole : components.Perm (group.components ++ (pre ++ post).flatMap Group.components) := by
    refine permuted.symm.trans ?_
    rw [splitIs, List.flatMap_append, List.flatMap_cons, List.flatMap_append]
    exact List.perm_append_comm_assoc _ _ _
  have othersApart : ∀ component ∈ (pre ++ post).flatMap Group.components, ∀ index ∈ group.restrictions,
      ¬ FreeIn index component := by
    have disjointHere := partition.disjoint
    rw [splitIs] at disjointHere
    obtain ⟨-, consPairwise, crossed⟩ := List.pairwise_append.mp disjointHere
    obtain ⟨groupFirst, -⟩ := List.pairwise_cons.mp consPairwise
    intro component inOthers index listed freeHere
    obtain ⟨other, otherMember, componentIn⟩ := List.mem_flatMap.mp inOthers
    have otherInGroups : other ∈ Mettapedia.GSLT.LanguageDef.RestrictionBlocks.groups ⟨count, components⟩ := by
      rw [splitIs]
      rcases List.mem_append.mp otherMember with inPre | inPost
      · exact List.mem_append_left _ inPre
      · exact List.mem_append_right _ (List.mem_cons_of_mem _ inPost)
    have used := partition.uses other otherInGroups component componentIn index freeHere
      (partition.inside group member index listed)
    rcases List.mem_append.mp otherMember with inPre | inPost
    · exact crossed other inPre group List.mem_cons_self index used listed
    · exact groupFirst other inPost index listed used
  have groupMembers : Members locatedCalc locatedBlock free (List.replicate count nameType ++ bound)
      group.components := fun element inGroup => members element (whole.symm.subset (List.mem_append_left _ inGroup))
  have moleculeWell : WellLocated isLoc (.bvar outer) (Prenex.molecule count group) :=
    (well.drop locVariables (dropped := []) whole (by simp)).part locVariables (partition.nodup group member)
      (partition.inside group member) (partition.uses group member) othersApart
  refine ⟨moleculeWell, part_members (language := locatedCalc) (block := locatedBlock) groupMembers
    (partition.uses group member), ?_, ?_⟩
  · refine Mettapedia.GSLT.LanguageDef.RestrictionBlocks.decompose_toPattern
      (fun component inMolecule => ComponentKind.decompose_atom (moleculeWell.kinds component inMolecule)) ?_
    intro index below
    have listedIndex : index < group.restrictions.length := below
    have listed : group.restrictions[index] ∈ group.restrictions := List.getElem_mem listedIndex
    obtain ⟨original, inGroup, freeHere⟩ := groups_covered ⟨count, components⟩ group member _ listed
    refine ⟨rename (Prenex.groupIndex count group.restrictions) original,
      List.mem_map.mpr ⟨original, inGroup, rfl⟩, ?_⟩
    have moved : Prenex.groupIndex count group.restrictions group.restrictions[index] = index := by
      simp only [Prenex.groupIndex, partition.inside group member _ listed, if_true]
      exact List.Nodup.idxOf_getElem (partition.nodup group member) _ _
    exact (Mettapedia.GSLT.LanguageDef.RestrictionBlocks.mentions_iff _ index).mpr
      ((Mettapedia.GSLT.LanguageDef.RestrictionBlocks.freeIn_rename original).mpr ⟨_, freeHere, moved⟩)
  · obtain ⟨first, firstMember⟩ := List.exists_mem_of_ne_nil _ (groups_nonempty ⟨count, components⟩ group member)
    obtain ⟨top, topMember, topPlace⟩ := moleculeWell.sits_at_place
      (List.mem_map.mpr ⟨first, firstMember, rfl⟩)
    exact ⟨top, topMember, by rw [topPlace]; simp [liftBVars, Prenex.molecule]⟩

/-! ## Replicated molecules -/

open Mettapedia.GSLT.LanguageDef.RestrictionBlocks (replicatedOf canonicalOf normal decompose decompose_canonicalOf
  canonicalOf_sound replicate_typed replicate_twice_equivalent replicate_fill replicate_bag_equivalent BaseContext
  size sizeList mass_le_size_toPattern body_congr body_typed restricts_typed decompose_sound)

/-- **The replicated component of a molecule**, as replication reads it: a lone replication stays one, since
`!!P = !P`; any other molecule is replicated whole, read canonically. -/
def replicatedEntry (form : Prenex) : Pattern :=
  match form.count, form.components with
  | 0, [.apply label [argument]] =>
      if label = locatedRepBlock.replicate then .apply label [canonicalOf locatedRepBlock argument]
      else .apply locatedRepBlock.replicate
        [canonicalOf locatedRepBlock (Prenex.toPattern locatedRepBlock.toBlock form)]
  | _, _ => .apply locatedRepBlock.replicate [canonicalOf locatedRepBlock (Prenex.toPattern locatedRepBlock.toBlock form)]

theorem replicatedOf_eq (inner : Prenex) :
    replicatedOf locatedRepBlock (canonicalOf locatedRepBlock) inner =
      (Mettapedia.GSLT.LanguageDef.RestrictionBlocks.groups inner).map fun group =>
        replicatedEntry (Prenex.molecule inner.count group) := rfl

/-- The fuel past which a molecule's replicated component reads back settled. -/
def entryFloor (form : Prenex) : Nat :=
  3 * (form.mass + (normal locatedRepBlock form).mass + innerWeight (form.components.headD inaction)) + 9

/-- **The replicated component of a molecule**: it sits at the molecule's place, its argument's block is
well-located there, it is typed, and it reads back as the replication of the molecule. -/
theorem replicated_entry {bound : List TypeExpr} {isLoc : Pattern → Prop} {outer : Nat} {form : Prenex}
    (well : WellLocated isLoc (.bvar outer) form) (locVariables : LocVariables isLoc)
    (context : BaseContext free bound)
    (members : Members locatedCalc locatedBlock free (List.replicate form.count nameType ++ bound) form.components)
    (decomposed : decompose locatedBlock (Prenex.toPattern locatedBlock form) = form)
    (sits : ∃ top ∈ form.components, placeAt top = some (.bvar (outer + form.count))) :
    ∃ argument, replicatedEntry form = .apply "LRep" [argument] ∧
      placeAt (.apply "LRep" [argument]) = some (.bvar outer) ∧
      WellLocated isLoc (.bvar outer) (decompose locatedBlock argument) ∧
      HasType locatedCalc free bound (.apply "LRep" [argument]) procType ∧
      ∀ fuel, entryFloor form ≤ fuel → ProcEquiv ambientCoreCalc ambientBlock free bound
        (.apply "ARep" [Prenex.toPattern ambientBlock (decodeForm fuel (.bvar outer) (decompose locatedBlock argument))])
        (.apply "ARep" [Prenex.toPattern ambientBlock (decodeForm fuel (.bvar outer) form)]) := by
  have signature : Mettapedia.GSLT.LanguageDef.RestrictionBlocks.BlockSignature locatedCalc locatedBlock :=
    Mettapedia.Languages.ProcessCalculi.Ambient.Located.locatedLanguage.toBlockSignature
  have fresh : locatedRepBlock.replicate ∉ locatedRepBlock.emptyUnits := by decide
  have restrictFresh : locatedRepBlock.replicate ≠ locatedRepBlock.restrict := by decide
  have formTyped : HasType locatedCalc free bound (Prenex.toPattern locatedBlock form) procType :=
    restricts_typed (language := locatedCalc) (block := locatedBlock) _ (body_typed members)
  -- the whole molecule replicated, read canonically
  have whole : ∃ argument, argument = canonicalOf locatedRepBlock (Prenex.toPattern locatedBlock form) ∧
      placeAt (.apply "LRep" [argument]) = some (.bvar outer) ∧
      WellLocated isLoc (.bvar outer) (decompose locatedBlock argument) ∧
      HasType locatedCalc free bound (.apply "LRep" [argument]) procType ∧
      ∀ fuel, entryFloor form ≤ fuel → ProcEquiv ambientCoreCalc ambientBlock free bound
        (.apply "ARep" [Prenex.toPattern ambientBlock (decodeForm fuel (.bvar outer) (decompose locatedBlock argument))])
        (.apply "ARep" [Prenex.toPattern ambientBlock (decodeForm fuel (.bvar outer) form)]) := by
    obtain ⟨normalWell, normalReads⟩ := decode_normal form well locVariables context members
    have argumentBlock : decompose locatedBlock (canonicalOf locatedRepBlock (Prenex.toPattern locatedBlock form)) =
        normal locatedRepBlock form := by
      rw [decompose_canonicalOf fresh restrictFresh]
      change normal locatedRepBlock (decompose locatedBlock (Prenex.toPattern locatedBlock form)) = _
      rw [decomposed]
    have placed : placeAt (.apply "LRep" [Prenex.toPattern locatedBlock form]) = some (.bvar outer) := by
      have unfolded : placeAt (.apply "LRep" [Prenex.toPattern locatedBlock form]) =
          outerPlace (2 * size (Prenex.toPattern locatedBlock form) + 2) form := by
        simp only [placeAt, size, sizeList]
        rw [show 2 * (size (Prenex.toPattern locatedBlock form) + 0 + 1) + 1 =
          (2 * size (Prenex.toPattern locatedBlock form) + 2) + 1 by omega]
        simp only [placeOf, if_true]
        rw [decomposed]
      rw [unfolded]
      obtain ⟨count, components⟩ := form
      refine outerPlace_well well sits fun component member => ?_
      have heavier := mass_le_size_toPattern (block := locatedBlock) (Prenex.mk count components)
      have inside := size_le_sizeList member
      simp only [Prenex.mass] at heavier
      omega
    refine ⟨_, rfl, placeAt_replicated_canonical placed (by
        rw [decomposed]
        exact normalWell), by rw [argumentBlock]; exact normalWell, ?_, fun fuel enough => ?_⟩
    · exact replicate_typed (language := locatedCalc) (block := locatedRepBlock)
        (canonicalOf_sound (language := locatedCalc) (block := locatedRepBlock) context formTyped).1
    · rw [argumentBlock]
      exact replicate_fill (language := ambientCoreCalc) (block := ambientRepBlock)
        (normalReads fuel (by unfold entryFloor at enough; omega) (by unfold entryFloor at enough; omega))
  obtain ⟨count, components⟩ := form
  unfold replicatedEntry
  split
  · -- a lone component: a replication stays one
    rename_i label argument countIs componentsIs
    simp only at countIs componentsIs
    subst countIs componentsIs
    split_ifs with isReplicate
    · change label = "LRep" at isReplicate
      subst isReplicate
      have member : Pattern.apply "LRep" [argument] ∈ [Pattern.apply "LRep" [argument]] := List.mem_singleton_self _
      obtain ⟨top, topMember, topPlace⟩ := sits
      rw [List.mem_singleton] at topMember
      subst topMember
      have placed : placeAt (.apply "LRep" [argument]) = some (.bvar outer) := by simpa using topPlace
      have innerWell : WellLocated isLoc (.bvar outer) (decompose locatedBlock argument) := by
        have inner := match well with
          | .intro _ _ _ _ _ _ reps _ _ _ _ _ => reps _ member argument (.bvar outer) rfl placed
        refine inner.mono (insideLoc_locVariables isLoc 0 _) (fun pattern isLocation => ?_) well.placeIsLoc
        have isVar := locVariables pattern isLocation
        cases pattern with
        | bvar index => simpa [insideLoc] using isLocation
        | fvar name => simpa [insideLoc] using isLocation
        | _ => simp [isVariable] at isVar
      have argumentTyped : HasType locatedCalc free bound argument procType := by
        have typed := members _ member
        simp only [List.replicate_zero, List.nil_append] at typed
        exact rep_inv typed
      obtain ⟨innerMembers, -⟩ := decompose_sound (language := locatedCalc) (block := locatedBlock) argumentTyped
      obtain ⟨normalWell, normalReads⟩ := decode_normal _ innerWell locVariables context innerMembers
      refine ⟨_, rfl, placeAt_replicated_canonical placed normalWell, by
          rw [decompose_canonicalOf fresh restrictFresh]; exact normalWell, ?_, fun fuel enough => ?_⟩
      · exact replicate_typed (language := locatedCalc) (block := locatedRepBlock)
          (canonicalOf_sound (language := locatedCalc) (block := locatedRepBlock) context argumentTyped).1
      · simp only [entryFloor, List.headD_cons, innerWeight] at enough
        obtain ⟨step, rfl⟩ : ∃ step, fuel = step + 3 := ⟨fuel - 3, by omega⟩
        rw [decompose_canonicalOf fresh restrictFresh]
        have read : Prenex.toPattern ambientBlock (decodeForm (step + 3) (.bvar outer)
            ⟨0, [.apply "LRep" [argument]]⟩) =
            .apply "ARep" [Prenex.toPattern ambientBlock (decodeForm step (.bvar outer)
              (decompose locatedBlock argument))] := by
          have here : placedAt (.bvar outer) (.apply "LRep" [argument]) = true := by
            simp [placedAt, placed]
          have lifted : liftBVars 0 0 (Pattern.bvar outer) = .bvar outer := by simp [liftBVars]
          simp only [decodeForm, readPlaced_succ, lifted, List.filter_cons_of_pos here, List.filter_nil,
            List.map_cons, List.map_nil, Prenex.toPattern, Prenex.restricts, Prenex.body]
          simp [readComponent, Prenex.toPattern, Prenex.body]
        rw [read]
        have settled := decodeForm_settled (.bvar outer) (decompose locatedBlock argument)
          (first := step + 3) (second := step) (by omega) (by omega)
        refine .trans _ _ _ (replicate_fill (language := ambientCoreCalc) (block := ambientRepBlock)
          (normalReads (step + 3) (by omega) (by omega))) ?_
        rw [settled]
        exact Relation.EqvGen.symm _ _ (replicate_twice_equivalent (language := ambientCoreCalc)
          (block := ambientRepBlock) (decodeForm_typed step (.bvar outer) innerMembers))
    · obtain ⟨argument, rfl, facts⟩ := whole
      exact ⟨_, rfl, facts⟩
  · obtain ⟨argument, rfl, facts⟩ := whole
    exact ⟨_, rfl, facts⟩

/-- **Replicated molecules read back as the replicated block**: the replicated components of a well-located block,
one per molecule, are well-located, typed, and read back as the replication of the block. -/
theorem decode_replicatedOf {bound : List TypeExpr} {isLoc : Pattern → Prop} {outer count : Nat}
    {components : List Pattern} (well : WellLocated isLoc (.bvar outer) ⟨count, components⟩)
    (locVariables : LocVariables isLoc) (context : BaseContext free bound)
    (members : Members locatedCalc locatedBlock free (List.replicate count nameType ++ bound) components) :
    WellLocated isLoc (.bvar outer)
        ⟨0, replicatedOf locatedRepBlock (canonicalOf locatedRepBlock) ⟨count, components⟩⟩ ∧
      Members locatedCalc locatedBlock free (List.replicate 0 nameType ++ bound)
        (replicatedOf locatedRepBlock (canonicalOf locatedRepBlock) ⟨count, components⟩) ∧
      ∃ least, ∀ fuel, least ≤ fuel → ProcEquiv ambientCoreCalc ambientBlock free bound
        (Prenex.toPattern ambientBlock (decodeForm (fuel + 3) (.bvar outer)
          ⟨0, replicatedOf locatedRepBlock (canonicalOf locatedRepBlock) ⟨count, components⟩⟩))
        (.apply "ARep" [Prenex.toPattern ambientBlock (decodeForm (fuel + 1) (.bvar outer) ⟨count, components⟩)]) := by
  rw [replicatedOf_eq]
  obtain ⟨partition, permuted⟩ := Mettapedia.GSLT.LanguageDef.RestrictionBlocks.groups_partition ⟨count, components⟩
  simp only at partition permuted
  set groupList := Mettapedia.GSLT.LanguageDef.RestrictionBlocks.groups (Prenex.mk count components) with groupListIs
  have entryFacts : ∀ group ∈ groupList, ∃ argument,
      replicatedEntry (Prenex.molecule count group) = .apply "LRep" [argument] ∧
      placeAt (.apply "LRep" [argument]) = some (.bvar outer) ∧
      WellLocated isLoc (.bvar outer) (decompose locatedBlock argument) ∧
      HasType locatedCalc free bound (.apply "LRep" [argument]) procType ∧
      ∀ fuel, entryFloor (Prenex.molecule count group) ≤ fuel → ProcEquiv ambientCoreCalc ambientBlock free bound
        (.apply "ARep" [Prenex.toPattern ambientBlock (decodeForm fuel (.bvar outer) (decompose locatedBlock argument))])
        (.apply "ARep" [Prenex.toPattern ambientBlock (decodeForm fuel (.bvar outer) (Prenex.molecule count group))]) := by
    intro group member
    obtain ⟨moleculeWell, moleculeMembers, decomposed, sits⟩ := molecule_facts well locVariables members member
    exact replicated_entry moleculeWell locVariables context moleculeMembers decomposed sits
  set entries := groupList.map fun group => replicatedEntry (Prenex.molecule count group) with entriesIs
  have entryOf : ∀ entry ∈ entries, ∃ group ∈ groupList, entry = replicatedEntry (Prenex.molecule count group) :=
    fun entry member => by
      obtain ⟨group, groupMember, rfl⟩ := List.mem_map.mp member
      exact ⟨group, groupMember, rfl⟩
  have entryShape : ∀ entry ∈ entries, ∃ argument, entry = .apply "LRep" [argument] ∧
      placeAt (.apply "LRep" [argument]) = some (.bvar outer) ∧
      WellLocated isLoc (.bvar outer) (decompose locatedBlock argument) ∧
      HasType locatedCalc free bound (.apply "LRep" [argument]) procType := by
    intro entry member
    obtain ⟨group, groupMember, rfl⟩ := entryOf entry member
    obtain ⟨argument, entryIs, placed, argumentWell, typed, -⟩ := entryFacts group groupMember
    exact ⟨argument, entryIs, placed, argumentWell, typed⟩
  have entriesMembers : Members locatedCalc locatedBlock free (List.replicate 0 nameType ++ bound) entries := by
    intro entry member
    obtain ⟨argument, rfl, -, -, typed⟩ := entryShape entry member
    simpa using typed
  have entriesWell : WellLocated isLoc (.bvar outer) ⟨0, entries⟩ := by
    refine .intro well.placeIsLoc (fun entry member => ?_) (fun entry member at' isPlaced => ?_) (fun index => ?_)
      (fun entry member name isName => ?_) (fun entry member label at' name continuation isCap listed => ?_)
      (fun entry member argument at' isRep isPlaced => ?_) (fun entry member argument isRep => ?_)
      ⟨id, fun entry member index child below childBelow isPlaced isChild => ?_⟩
      (fun entry member message isMsgOf => ?_) (fun entry member at' message continuation isCapComponent => ?_)
      (fun entry member label at' binder body isInput listed => ?_)
    · obtain ⟨argument, rfl, -, -, -⟩ := entryShape entry member
      exact .replication
    · obtain ⟨argument, rfl, placed, -, -⟩ := entryShape entry member
      rw [placed, Option.some.injEq] at isPlaced
      exact .inl (by rw [← isPlaced]; simp [liftBVars])
    · rw [List.filter_eq_nil_iff.mpr fun entry member isChild => by
        obtain ⟨argument, rfl, -, -, -⟩ := entryShape entry member
        simp [childOf] at isChild]
      simp
    · obtain ⟨argument, rfl, -, -, -⟩ := entryShape entry member
      simp [nameOf] at isName
    · obtain ⟨argument, rfl, -, -, -⟩ := entryShape entry member
      simp at isCap
    · obtain ⟨argument', rfl, placed, argumentWell, -⟩ := entryShape entry member
      simp only [Pattern.apply.injEq, List.cons.injEq, and_true, true_and] at isRep
      subst isRep
      rw [placed, Option.some.injEq] at isPlaced
      subst isPlaced
      refine argumentWell.mono locVariables (fun pattern inside => ?_) well.placeIsLoc
      cases pattern with
      | bvar index => simpa [insideLoc] using inside
      | fvar name => simpa [insideLoc] using inside
      | _ => simp [insideLoc] at inside
    · obtain ⟨argument', rfl, placed, -, -⟩ := entryShape entry member
      simp only [Pattern.apply.injEq, List.cons.injEq, and_true, true_and] at isRep
      subst isRep
      rw [placed]
      rfl
    · obtain ⟨argument, rfl, -, -, -⟩ := entryShape entry member
      simp [childOf] at isChild
    · obtain ⟨argument, rfl, -, -, -⟩ := entryShape entry member
      simp [messageOf] at isMsgOf
    · obtain ⟨argument, rfl, -, -, -⟩ := entryShape entry member
      simp at isCapComponent
    · obtain ⟨argument, rfl, -, -, -⟩ := entryShape entry member
      simp at isInput
  refine ⟨entriesWell, entriesMembers, ?_⟩
  set floor := (groupList.map fun group => entryFloor (Prenex.molecule count group)).sum with floorIs
  refine ⟨floor, fun fuel enough => ?_⟩
  have floorOf : ∀ group ∈ groupList, entryFloor (Prenex.molecule count group) ≤ fuel := fun group member =>
    le_trans (List.le_sum_of_mem (List.mem_map_of_mem (f := fun group => entryFloor (Prenex.molecule count group))
      member)) enough
  -- every replicated component sits at the place and reads as the replication of its argument's block
  have lifted : liftBVars 0 0 (Pattern.bvar outer) = .bvar outer := by simp [liftBVars]
  have allHere : entries.filter (placedAt (.bvar outer)) = entries := List.filter_eq_self.mpr fun entry member => by
    obtain ⟨argument, rfl, placed, -, -⟩ := entryShape entry member
    simp [placedAt, placed]
  have noneElsewhere : (entries.filter fun other => !placedAt (.bvar outer) other) = [] :=
    List.filter_eq_nil_iff.mpr fun entry member => by
      obtain ⟨argument, rfl, placed, -, -⟩ := entryShape entry member
      simp [placedAt, placed]
  have read : Prenex.toPattern ambientBlock (decodeForm (fuel + 3) (.bvar outer) ⟨0, entries⟩) =
      Prenex.body ambientBlock (entries.map fun entry => readComponent (fuel + 1) (.bvar outer) entry []) := by
    simp only [decodeForm, lifted, readPlaced_succ, allHere, noneElsewhere, Prenex.toPattern, Prenex.restricts]
  rw [read]
  -- the replications of the molecules
  have moleculeMembers : ∀ group ∈ groupList, Members locatedCalc locatedBlock free
      (List.replicate (Prenex.molecule count group).count nameType ++ bound) (Prenex.molecule count group).components :=
    fun group member => (molecule_facts well locVariables members member).2.1
  have pointwise : List.Forall₂ (ProcEquiv ambientCoreCalc ambientBlock free bound)
      (entries.map fun entry => readComponent (fuel + 1) (.bvar outer) entry [])
      (groupList.map fun group => .apply "ARep" [Prenex.toPattern ambientBlock
        (decodeForm (fuel + 1) (.bvar outer) (Prenex.molecule count group))]) := by
    rw [entriesIs, List.map_map]
    refine forall₂_map_map fun group member => ?_
    obtain ⟨argument, entryIs, -, -, -, reads⟩ := entryFacts group member
    have floorHere := floorOf group member
    simp only [Function.comp_apply, entryIs]
    have settled := decodeForm_settled (.bvar outer) (Prenex.molecule count group) (first := fuel)
      (second := fuel + 1) (by unfold entryFloor at floorHere; omega) (by unfold entryFloor at floorHere; omega)
    rw [← settled]
    simpa [readComponent] using reads fuel floorHere
  have readMembers : Members ambientCoreCalc ambientBlock free bound
      (entries.map fun entry => readComponent (fuel + 1) (.bvar outer) entry []) := by
    intro element member
    obtain ⟨entry, inEntries, rfl⟩ := List.mem_map.mp member
    exact (decode_typed (fuel + 1)).2.2 _ _ _ (by simpa using entriesMembers entry inEntries) Members.nil
  have moleculeReads : Members ambientCoreCalc ambientBlock free bound (groupList.map fun group =>
      Prenex.toPattern ambientBlock (decodeForm (fuel + 1) (.bvar outer) (Prenex.molecule count group))) := by
    intro element member
    obtain ⟨group, groupMember, rfl⟩ := List.mem_map.mp member
    exact decodeForm_typed (fuel + 1) (.bvar outer) (moleculeMembers group groupMember)
  have replicatedReads := replicate_bag_equivalent (language := ambientCoreCalc) (block := ambientRepBlock) moleculeReads
  rw [List.map_map] at replicatedReads
  have whole : WellLocated isLoc (.bvar outer) ⟨count, groupList.flatMap Group.components⟩ :=
    well.drop locVariables (dropped := []) permuted.symm (by simp)
  have wholeMembers : Members locatedCalc locatedBlock free (List.replicate count nameType ++ bound)
      (groupList.flatMap Group.components) := fun element member => members element (permuted.subset member)
  have split := decode_partition (free := free) locVariables fuel partition whole wholeMembers
  have reordered := decode_perm (free := free) fuel (.bvar outer) permuted wholeMembers
  refine .trans _ _ _ (body_congr readMembers pointwise) ?_
  refine .trans _ _ _ (Relation.EqvGen.symm _ _ (bag_body_equivalent (language := ambientCoreCalc) (block := ambientBlock)
    (fun element member => by
      obtain ⟨group, groupMember, rfl⟩ := List.mem_map.mp member
      exact replicate_typed (language := ambientCoreCalc) (block := ambientRepBlock)
        (moleculeReads _ (List.mem_map_of_mem groupMember))))) ?_
  refine .trans _ _ _ (Relation.EqvGen.symm _ _ replicatedReads) ?_
  exact replicate_fill (language := ambientCoreCalc) (block := ambientRepBlock)
    (.trans _ _ _ (Relation.EqvGen.symm _ _ split) reordered)

end Mettapedia.Languages.ProcessCalculi.Ambient.Decoding
