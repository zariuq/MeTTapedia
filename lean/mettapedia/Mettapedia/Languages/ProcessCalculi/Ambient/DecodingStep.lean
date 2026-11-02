import Mettapedia.Languages.ProcessCalculi.Ambient.DecodingParts

/-!
# Reading back one absorption

One absorption of a well-located block drops a copy of a replicated component's argument with the restrictions only the
copy uses (`absorbOnce_shape`). Read back, the block with the copy is the block without it: the copy's restrictions
come innermost (`decode_narrow`), they move down into the ambients holding the copy and the copy is absorbed by the
replication there (`absorb_core`), and the restrictions left unused drop (`decode_drop`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.Ambient.Decoding

open Mettapedia.Languages.ProcessCalculi.Ambient.Comm (ambientCoreCalc)

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Substitution (liftBVars)
open Mettapedia.OSLF.MeTTaIL.CanonicalBags (FreeIn)
open Mettapedia.GSLT.LanguageDef.WellSorted (HasType FreeTypeContext)
open Mettapedia.GSLT.LanguageDef.RestrictionBlocks (Prenex Members ProcEquiv Group rename outsideOf copyOf canonicalOf
  absorbOnce groupsThrough groupsThrough_partition groupsThrough_map mentions mentions_iff mem_restrictionsOf
  throughKeys mem_usedRestrictions asGroup IsOrder splitOrder outside_parts first_part_renaming outside_unused
  lowerAbove rename_id restricts_add mem_outsideOf restricts_congr)
open Mettapedia.Languages.ProcessCalculi.Ambient.Full (ambientBlock)
open Mettapedia.Languages.ProcessCalculi.Ambient.Located (locatedCalc locatedBlock locatedRepBlock)
open Mettapedia.Languages.ProcessCalculi.Ambient.Encoding (nameType procType)

variable {free : FreeTypeContext}

/-- **What one absorption finds**: a replicated component; a group of the other components, linked through the
restrictions the replicated component does not use and owning those it uses, whose copy reads canonically as the
replicated argument; and the rest, the replicated component among it. -/
theorem absorbOnce_shape {count : Nat} {components : List Pattern} {next : Prenex}
    (absorbed : absorbOnce locatedRepBlock (canonicalOf locatedRepBlock) ⟨count, components⟩ = some next) :
    ∃ (argument : Pattern) (group : Group) (kept : List Pattern),
      Pattern.apply "LRep" [argument] ∈ components ∧ Pattern.apply "LRep" [argument] ∈ kept ∧
      components.Perm (group.components ++ kept) ∧
      (∀ component ∈ kept, ∀ index ∈ group.restrictions, ¬ FreeIn index component) ∧
      group.restrictions.Nodup ∧ (∀ index ∈ group.restrictions, index < count) ∧
      (∀ index ∈ group.restrictions, mentions index (.apply "LRep" [argument]) = false) ∧
      (∀ component ∈ group.components, ∀ index < count, FreeIn index component →
        mentions index (.apply "LRep" [argument]) = false → index ∈ group.restrictions) ∧
      (∀ index ∈ group.restrictions, ∃ component ∈ group.components, FreeIn index component) ∧
      canonicalOf locatedRepBlock (copyOf locatedBlock count group) =
        canonicalOf locatedRepBlock (rename (Prenex.groupIndex count (outsideOf count group.restrictions)) argument) ∧
      next = ⟨count, kept⟩ := by
  unfold absorbOnce at absorbed
  obtain ⟨position, positionIn, found⟩ := List.exists_of_findSome?_eq_some absorbed
  have inside : position < components.length := List.mem_range.mp positionIn
  simp only [List.getElem?_eq_getElem inside] at found
  split at found
  swap
  · cases found
  rename_i label argument isAt
  have componentIs : components[position] = .apply label [argument] := Option.some.inj isAt
  split_ifs at found with isReplicate
  subst isReplicate
  obtain ⟨group, groupFound, rfl⟩ := Option.map_eq_some_iff.mp found
  set replicated : Pattern := .apply locatedRepBlock.replicate [argument] with replicatedIs
  set allowed := (List.range count).filter fun index => !mentions index replicated with allowedIs
  set candidates := groupsThrough allowed count (components.eraseIdx position) with candidatesIs
  have groupMember := List.mem_of_find?_eq_some groupFound
  have copyFound := List.find?_some groupFound
  obtain ⟨partition, permuted⟩ := groupsThrough_partition allowed count (components.eraseIdx position)
  set kept := (candidates.erase group).flatMap Group.components ++ [replicated] with keptIs
  have split : components.Perm (group.components ++ kept) := by
    have around : (replicated :: components.eraseIdx position).Perm components := by
      rw [← componentIs]
      exact List.getElem_cons_eraseIdx_perm inside
    have regroup : (components.eraseIdx position).Perm
        (group.components ++ (candidates.erase group).flatMap Group.components) :=
      permuted.symm.trans (by simpa using (List.perm_cons_erase groupMember).flatMap_right Group.components)
    have moved := (List.perm_append_singleton replicated
      (group.components ++ (candidates.erase group).flatMap Group.components)).symm
    rw [keptIs, ← List.append_assoc]
    exact around.symm.trans ((regroup.cons replicated).trans moved)
  have apart : ∀ component ∈ kept, ∀ index ∈ group.restrictions, ¬ FreeIn index component := by
    intro component member index listed freeHere
    have permitted := partition.allowedOnly group groupMember index listed
    rcases List.mem_append.mp member with inGroups | inReplicated
    · obtain ⟨other, otherMember, componentIn⟩ := List.mem_flatMap.mp inGroups
      have otherIn := List.mem_of_mem_erase otherMember
      have used := partition.uses other otherIn component componentIn index permitted freeHere
        (partition.inside group groupMember index listed)
      by_cases same : other = group
      · subst same
        exact Mettapedia.GSLT.LanguageDef.RestrictionBlocks.pairwise_self_of_mem_erase partition.disjoint otherMember
          index listed listed
      · exact partition.disjoint.forall groupMember otherIn (Ne.symm same) index listed used
    · rw [List.mem_singleton] at inReplicated
      subst inReplicated
      have unmentioned := (List.mem_filter.mp permitted).2
      simp only [Bool.not_eq_true'] at unmentioned
      rw [(mentions_iff _ index).mpr freeHere] at unmentioned
      exact Bool.noConfusion unmentioned
  have covered : ∀ index ∈ group.restrictions, ∃ component ∈ group.components, FreeIn index component := by
    have mapped := groupsThrough_map allowed count id (components.eraseIdx position)
    rw [List.map_id] at mapped
    have asMember := groupMember
    rw [candidatesIs, mapped] at asMember
    obtain ⟨items, -, same⟩ := List.mem_map.mp asMember
    rw [← same]
    intro index listed
    obtain ⟨item, inItems, keyed⟩ := mem_restrictionsOf.mp listed
    simp only [throughKeys, List.mem_filter, mem_usedRestrictions] at keyed
    exact ⟨item, by simpa [asGroup] using inItems, (mentions_iff item index).mp keyed.1.2⟩
  have tested := copyFound
  simp only [Bool.and_eq_true, beq_iff_eq] at tested
  refine ⟨argument, group, kept, ?_, List.mem_append_right _ (List.mem_singleton_self _), split, apart,
    partition.nodup group groupMember, partition.inside group groupMember, ?_, ?_, covered, tested.1.1.1, rfl⟩
  · show replicated ∈ components
    rw [← componentIs]
    exact List.getElem_mem inside
  · intro index listed
    have permitted := (List.mem_filter.mp (partition.allowedOnly group groupMember index listed)).2
    show mentions index replicated = false
    simpa using permitted
  · intro component member index below freeHere unmentioned
    change mentions index replicated = false at unmentioned
    exact partition.uses group groupMember component member index
      (List.mem_filter.mpr ⟨List.mem_range.mpr below, by simpa using unmentioned⟩) freeHere below

/-! ## Reading back reordered and narrowed blocks -/

/-- **Components in another order read back equivalently.** -/
theorem decode_perm {bound : List TypeExpr} (fuel : Nat) (place : Pattern) {count : Nat} {first second : List Pattern}
    (permutation : first.Perm second)
    (members : Members locatedCalc locatedBlock free (List.replicate count nameType ++ bound) first) :
    ProcEquiv ambientCoreCalc ambientBlock free bound
      (Prenex.toPattern ambientBlock (decodeForm (fuel + 1) place ⟨count, first⟩))
      (Prenex.toPattern ambientBlock (decodeForm (fuel + 1) place ⟨count, second⟩)) := by
  simp only [decodeForm, Prenex.toPattern]
  exact restricts_congr (language := ambientCoreCalc) (block := ambientBlock) count
    (readPlaced_perm fuel (liftBVars 0 count place) permutation members)

/-- **A block read with some of its restrictions innermost**: those a part of its components owns, the rest of the
block renumbered outside them. -/
theorem decode_narrow {bound : List TypeExpr} (fuel : Nat) (place : Pattern) {count : Nat} {restrictions : List Nat}
    (nodup : restrictions.Nodup) (inside : ∀ index ∈ restrictions, index < count) {rest part : List Pattern}
    (members : Members locatedCalc locatedBlock free (List.replicate count nameType ++ bound) (rest ++ part))
    (apart : ∀ component ∈ rest, ∀ index ∈ restrictions, ¬ FreeIn index component) :
    ProcEquiv ambientCoreCalc ambientBlock free bound
      (Prenex.toPattern ambientBlock (decodeForm (fuel + 1) place ⟨count, rest ++ part⟩))
      (Prenex.restricts ambientBlock (outsideOf count restrictions).length
        (Prenex.restricts ambientBlock restrictions.length (Prenex.body ambientBlock
          (readPlaced fuel (liftBVars 0 restrictions.length (liftBVars 0 (outsideOf count restrictions).length place))
            ((rest.map (rename (Prenex.groupIndex count (outsideOf count restrictions)))).map
                (liftBVars 0 restrictions.length) ++
              part.map (rename (Prenex.permute count (splitOrder count (outsideOf count restrictions)
                restrictions)))))))) := by
  set others := outsideOf count restrictions with othersIs
  have parts := outside_parts nodup inside
  have total : restrictions.length + others.length = count := by
    have counted := parts.lengths
    rw [outside_unused, List.length_nil, Nat.add_zero] at counted
    exact counted
  set order := splitOrder count others restrictions with orderIs
  have isOrder : IsOrder count order := parts.splitOrder_perm
  have restUses : ∀ component ∈ rest, ∀ index, FreeIn index component → index < count → index ∈ others := by
    intro component member index freeHere below
    exact mem_outsideOf.mpr ⟨below, fun listed => apart component member index listed freeHere⟩
  have lifted : rest.map (rename (Prenex.permute count order)) =
      (rest.map (rename (Prenex.groupIndex count others))).map (liftBVars 0 restrictions.length) := by
    rw [List.map_map]
    apply List.map_congr_left
    intro component member
    have identity := first_part_renaming parts (restUses component member)
    rw [outside_unused] at identity
    have lowerZero : lowerAbove (restrictions.length + others.length) 0 = id := by
      funext index
      simp only [lowerAbove, Nat.sub_zero, id]
      split_ifs <;> rfl
    rw [List.length_nil, lowerZero, rename_id] at identity
    exact identity
  have reordered := decode_reorder (free := free) fuel place isOrder members
  rw [List.map_append, lifted] at reordered
  refine .trans _ _ _ (Relation.EqvGen.symm _ _ reordered) ?_
  simp only [decodeForm, Prenex.toPattern]
  rw [restricts_add, liftBVars_par_outer, show others.length + restrictions.length = count by omega]
  exact .refl _

/-! ## Reading back one absorption -/

open Mettapedia.GSLT.LanguageDef.RestrictionBlocks (normal decompose_toPattern decompose_canonicalOf decompose_sound
  size sizeList sizeList_perm sizeList_append sizeList_map_rename mass_decompose size_rename inverse inverse_isOrder
  permute_inverse permute_injective permute_lt permute_of_ge orders_reorders orders_complete block_reorder_equivalent
  part_members splitPlace BlockSignature freeIn_rename rename_comp rename_apply rename_bvar liftBVars_eq_rename
  shiftAbove decompose_renameOuter BaseContext)
open Mettapedia.Languages.ProcessCalculi.Ambient.Located (locatedLanguage)

/-- **What normalizing a block keeps**: a well-located typed block has a well-located canonical block, which reads
back as the block. -/
def NormalFacts (free : FreeTypeContext) (form : Prenex) : Prop :=
  ∀ {isLoc : Pattern → Prop} {outer : Nat} {bound : List TypeExpr},
    WellLocated isLoc (.bvar outer) form → LocVariables isLoc → BaseContext free bound →
    Members locatedCalc locatedBlock free (List.replicate form.count nameType ++ bound) form.components →
    WellLocated isLoc (.bvar outer) (normal locatedRepBlock form) ∧
      ∀ fuel, 3 * form.mass + 3 ≤ fuel → 3 * (normal locatedRepBlock form).mass + 3 ≤ fuel →
        ProcEquiv ambientCoreCalc ambientBlock free bound
          (Prenex.toPattern ambientBlock (decodeForm fuel (.bvar outer) (normal locatedRepBlock form)))
          (Prenex.toPattern ambientBlock (decodeForm fuel (.bvar outer) form))

/-- **What normalizing keeps**, for the blocks lighter than a weight. -/
def NormalBelow (free : FreeTypeContext) (weight : Nat) : Prop :=
  ∀ (form : Prenex), form.mass < weight → NormalFacts free form

/-- A component of a located block is its own block. -/
theorem ComponentKind.decompose_atom {count : Nat} {component : Pattern} (kind : ComponentKind count component) :
    Mettapedia.GSLT.LanguageDef.RestrictionBlocks.decompose locatedBlock component = Prenex.atom component := by
  refine Mettapedia.GSLT.LanguageDef.RestrictionBlocks.decompose_atom ?_ ?_ ?_ ?_
  all_goals cases kind <;> simp

/-- **One absorption reads back as nothing**: a well-located block with a copy group of a replicated component's
argument reads back as the block without it, when the lighter blocks read back as their canonical forms. -/
theorem decode_absorb_step {bound : List TypeExpr} {isLoc : Pattern → Prop} {outer count : Nat}
    {components kept : List Pattern} {argument : Pattern} {group : Group}
    (well : WellLocated isLoc (.bvar outer) ⟨count, components⟩) (locVariables : LocVariables isLoc)
    (context : BaseContext free bound)
    (members : Members locatedCalc locatedBlock free (List.replicate count nameType ++ bound) components)
    (repMember : Pattern.apply "LRep" [argument] ∈ components) (repKept : Pattern.apply "LRep" [argument] ∈ kept)
    (split : components.Perm (group.components ++ kept))
    (apart : ∀ component ∈ kept, ∀ index ∈ group.restrictions, ¬ FreeIn index component)
    (ownedNodup : group.restrictions.Nodup) (ownedInside : ∀ index ∈ group.restrictions, index < count)
    (allowedOnly : ∀ index ∈ group.restrictions, mentions index (.apply "LRep" [argument]) = false)
    (covers : ∀ component ∈ group.components, ∀ index < count, FreeIn index component →
      mentions index (.apply "LRep" [argument]) = false → index ∈ group.restrictions)
    (covered : ∀ index ∈ group.restrictions, ∃ component ∈ group.components, FreeIn index component)
    (copied : canonicalOf locatedRepBlock (copyOf locatedBlock count group) =
      canonicalOf locatedRepBlock (rename (Prenex.groupIndex count (outsideOf count group.restrictions)) argument))
    (normalBelow : NormalBelow free (Prenex.mk count components).mass) :
    WellLocated isLoc (.bvar outer) ⟨count, kept⟩ ∧
      ∃ least, ∀ fuel, least ≤ fuel → ProcEquiv ambientCoreCalc ambientBlock free bound
        (Prenex.toPattern ambientBlock (decodeForm fuel (.bvar outer) ⟨count, components⟩))
        (Prenex.toPattern ambientBlock (decodeForm fuel (.bvar outer) ⟨count, kept⟩)) := by
  have signature : BlockSignature locatedCalc locatedBlock := locatedLanguage.toBlockSignature
  -- the replicated component's place
  obtain ⟨at', repPlace⟩ : ∃ at', placeAt (.apply "LRep" [argument]) = some at' :=
    Option.isSome_iff_exists.mp (well.repsPlaced _ repMember argument rfl)
  obtain ⟨repIndex, rfl⟩ : ∃ repIndex, at' = .bvar repIndex := by
    rcases well.placed _ repMember at' repPlace with same | ⟨index, -, same, -⟩
    · exact ⟨outer + count, by simpa [liftBVars] using same⟩
    · exact ⟨index, same⟩
  have inComponents : ∀ component ∈ group.components, component ∈ components :=
    fun component member => split.symm.subset (List.mem_append_left _ member)
  have keptComponents : ∀ component ∈ kept, component ∈ components :=
    fun component member => split.symm.subset (List.mem_append_right _ member)
  have places := copy_places well repMember repPlace inComponents ownedNodup ownedInside allowedOnly covers copied
  have children := copy_children well repMember repPlace split apart ownedNodup ownedInside allowedOnly covers copied
  -- the block without the group is well-located
  have nextWell : WellLocated isLoc (.bvar outer) ⟨count, kept⟩ := by
    refine well.drop locVariables split fun component member index isPlaced marker inGroup isChild => ?_
    obtain ⟨owned, listed, same⟩ := children marker inGroup _ isChild
    simp only [Pattern.bvar.injEq] at same
    subst same
    exact apart component member index listed (freeIn_placeAt isPlaced)
  refine ⟨nextWell, ?_⟩
  -- the reordering that puts the group's restrictions innermost
  set owned := group.restrictions.length with ownedIs
  set others := outsideOf count group.restrictions with othersIs
  set order := splitOrder count others group.restrictions with orderIs
  have parts := outside_parts ownedNodup ownedInside
  have total : owned + others.length = count := by
    have counted := parts.lengths
    rw [outside_unused, List.length_nil, Nat.add_zero] at counted
    exact counted
  have isOrder : IsOrder count order := parts.splitOrder_perm
  have keptUses : ∀ component ∈ kept, ∀ index, FreeIn index component → index < count → index ∈ others := by
    intro component member index freeHere below
    exact mem_outsideOf.mpr ⟨below, fun listed => apart component member index listed freeHere⟩
  have keptMoved : ∀ component ∈ kept, rename (Prenex.permute count order) component =
      liftBVars 0 owned (rename (Prenex.groupIndex count others) component) := by
    intro component member
    have identity := first_part_renaming parts (keptUses component member)
    rw [outside_unused] at identity
    have lowerZero : lowerAbove (owned + others.length) 0 = id := by
      funext index
      simp only [lowerAbove, Nat.sub_zero, id]
      split_ifs <;> rfl
    rw [List.length_nil, lowerZero, rename_id] at identity
    exact identity
  have ownedMoved : ∀ index ∈ group.restrictions,
      Prenex.permute count order index = group.restrictions.idxOf index := by
    intro index listed
    have below := ownedInside index listed
    simp only [Prenex.permute, below, if_true, orderIs, splitOrder]
    rw [List.getD_eq_getElem _ _ (by simp [below]), List.getElem_map, List.getElem_range]
    simp [splitPlace, listed]
  have ownedBelow : ∀ index ∈ group.restrictions, Prenex.permute count order index < owned := by
    intro index listed
    rw [ownedMoved index listed]
    exact List.idxOf_lt_length_iff.mpr listed
  -- the components, the group's restrictions innermost
  set keptLow := kept.map (rename (Prenex.groupIndex count others)) with keptLowIs
  set copyParts := group.components.map (rename (Prenex.permute count order)) with copyPartsIs
  have lifted : kept.map (rename (Prenex.permute count order)) = keptLow.map (liftBVars 0 owned) := by
    rw [keptLowIs, List.map_map]
    exact List.map_congr_left fun component member => keptMoved component member
  set argumentLow := rename (Prenex.groupIndex count others) argument with argumentLowIs
  set home := rename (Prenex.groupIndex count others) (.bvar repIndex) with homeIs
  have repLow : Pattern.apply "LRep" [argumentLow] ∈ keptLow :=
    List.mem_map.mpr ⟨_, repKept, by simp [argumentLowIs, rename_apply]⟩
  have homePlace : placeAt (.apply "LRep" [argumentLow]) = some home := by
    rw [show Pattern.apply "LRep" [argumentLow] = rename (Prenex.groupIndex count others) (.apply "LRep" [argument]) by
      simp [argumentLowIs, rename_apply], placeAt_rename, repPlace, Option.map_some]
  have repMoved : rename (Prenex.permute count order) (.bvar repIndex) = liftBVars 0 owned home := by
    have moved := congrArg placeAt (keptMoved _ repKept)
    rw [placeAt_rename, repPlace, Option.map_some, liftBVars_eq_rename, placeAt_rename, placeAt_rename, repPlace,
      Option.map_some, Option.map_some, Option.some.injEq] at moved
    rw [moved, homeIs, liftBVars_eq_rename]
  have copyPlaced : ∀ component ∈ copyParts, ∀ spot, placeAt component = some spot →
      spot = liftBVars 0 owned home ∨ ∃ index < owned, spot = .bvar index := by
    intro component member spot isPlaced
    obtain ⟨original, inGroup, rfl⟩ := List.mem_map.mp member
    rw [placeAt_rename] at isPlaced
    obtain ⟨originalSpot, found, rfl⟩ := Option.map_eq_some_iff.mp isPlaced
    rcases places original inGroup originalSpot found with rfl | ⟨index, listed, rfl⟩
    · exact .inl repMoved
    · exact .inr ⟨_, ownedBelow index listed, by rw [rename_bvar]⟩
  have copyChildren : ∀ component ∈ copyParts, ∀ child, childOf component = some child →
      ∃ index < owned, child = .bvar index := by
    intro component member child isChild
    obtain ⟨original, inGroup, rfl⟩ := List.mem_map.mp member
    rw [childOf_rename] at isChild
    obtain ⟨originalChild, found, rfl⟩ := Option.map_eq_some_iff.mp isChild
    obtain ⟨index, listed, rfl⟩ := children original inGroup originalChild found
    exact ⟨_, ownedBelow index listed, by rw [rename_bvar]⟩
  -- typing
  have permutedMembers : Members locatedCalc locatedBlock free (List.replicate count nameType ++ bound)
      (kept ++ group.components) :=
    fun element member => members element ((split.trans List.perm_append_comm).symm.subset member)
  obtain ⟨reorderedMembers, -⟩ := block_reorder_equivalent (language := locatedCalc) (block := locatedBlock)
    (bound := bound) (orders_reorders (List.range count) order (orders_complete _ _ isOrder)) permutedMembers
  have reorderedIs : (kept ++ group.components).map (rename (Prenex.permute count order)) =
      keptLow.map (liftBVars 0 owned) ++ copyParts := by rw [List.map_append, lifted]
  rw [reorderedIs] at reorderedMembers
  have splitContext : List.replicate count nameType ++ bound =
      List.replicate owned nameType ++ (List.replicate others.length nameType ++ bound) := by
    rw [← List.append_assoc, ← List.replicate_add, total]
  have copyMembers : Members locatedCalc locatedBlock free
      (List.replicate owned nameType ++ (List.replicate others.length nameType ++ bound)) copyParts := by
    intro element member
    have typed := reorderedMembers element (List.mem_append_right _ member)
    rw [splitContext] at typed
    exact typed
  have keptMembers : Members locatedCalc locatedBlock free (List.replicate count nameType ++ bound) kept :=
    fun element member => members element (keptComponents element member)
  have keptLowMembers : Members locatedCalc locatedBlock free (List.replicate others.length nameType ++ bound)
      keptLow := part_members (language := locatedCalc) (block := locatedBlock) keptMembers keptUses
  -- the reordered block and the block left, lowered, are well-located
  have permutedWell : WellLocated isLoc (.bvar outer) ⟨count, kept ++ group.components⟩ :=
    well.drop locVariables (dropped := []) (split.trans List.perm_append_comm) (by simp)
  have reorderedWell : WellLocated isLoc (.bvar outer) ⟨count, keptLow.map (liftBVars 0 owned) ++ copyParts⟩ := by
    rw [← reorderedIs]
    refine WellLocated.comap (relabel := Prenex.permute count (inverse count order))
      (permute_injective (inverse_isOrder isOrder)) (fun index below => permute_lt (inverse_isOrder isOrder) below)
      (fun offset => permute_of_ge _ (by omega)) ?_ locVariables
    rw [List.map_map]
    have back : (rename (Prenex.permute count (inverse count order)) ∘ rename (Prenex.permute count order)) = id := by
      funext pattern
      simp only [Function.comp, id, rename_comp, permute_inverse isOrder, rename_id]
    rw [back, List.map_id]
    exact permutedWell
  have othersNodup : others.Nodup := List.nodup_range.filter _
  have othersInside : ∀ index ∈ others, index < count := fun index member => (mem_outsideOf.mp member).1
  have keptLowWell : WellLocated isLoc (.bvar outer) ⟨others.length, keptLow⟩ := by
    refine WellLocated.comap (relabel := ungroup count others) (ungroup_injective othersNodup othersInside)
      (fun index below => by
        simp only [ungroup, below, if_true]
        rw [List.getD_eq_getElem _ _ below]
        exact othersInside _ (List.getElem_mem below))
      (fun offset => by simp only [ungroup]; split_ifs <;> omega) ?_ locVariables
    rw [keptLowIs, ungroup_restores othersInside keptUses]
    exact nextWell
  -- the copy and the argument, read at the replicated component's place
  have homeLoc : insideLoc isLoc count (keptLow.map (liftBVars 0 owned) ++ copyParts) (liftBVars 0 owned home) := by
    refine reorderedWell.placeInside locVariables (liftBVars 0 owned (.apply "LRep" [argumentLow]))
      (List.mem_append_left _ (List.mem_map.mpr ⟨_, repLow, rfl⟩)) _ ?_
    rw [liftBVars_eq_rename, placeAt_rename, homePlace, Option.map_some, liftBVars_eq_rename]
  have copyWell := reorderedWell.innerPart (owned := owned) (home := home) (by omega)
    (fun component member index below free => by
      obtain ⟨original, -, rfl⟩ := List.mem_map.mp member
      rw [liftBVars_eq_rename] at free
      obtain ⟨source, -, image⟩ := (freeIn_rename original).mp free
      simp only [shiftAbove, Nat.not_lt_zero, if_false] at image
      omega) copyPlaced copyChildren homeLoc
  have copyLocVariables : LocVariables
      (fun pattern => insideLoc isLoc count (keptLow.map (liftBVars 0 owned) ++ copyParts) (liftBVars 0 owned pattern)) := by
    intro pattern inside
    have isVar := insideLoc_locVariables isLoc count _ _ inside
    rwa [isVariable_lift] at isVar
  have argumentWell : WellLocated
      (fun pattern => insideLoc isLoc count (keptLow.map (liftBVars 0 owned) ++ copyParts) (liftBVars 0 owned pattern))
      home (Mettapedia.GSLT.LanguageDef.RestrictionBlocks.decompose locatedBlock argumentLow) := by
    have repInner : WellLocated (insideLoc isLoc count (keptLow.map (liftBVars 0 owned) ++ copyParts))
        (liftBVars 0 owned home)
        (Mettapedia.GSLT.LanguageDef.RestrictionBlocks.decompose locatedBlock (liftBVars 0 owned argumentLow)) := by
      cases reorderedWell with
      | intro _ _ _ _ _ _ reps _ _ _ _ _ =>
          exact reps _ (List.mem_append_left _ (List.mem_map.mpr ⟨_, repLow, rfl⟩)) (liftBVars 0 owned argumentLow)
            (liftBVars 0 owned home) (by simp [liftBVars])
            (by rw [liftBVars_eq_rename, placeAt_rename, homePlace, Option.map_some, liftBVars_eq_rename])
    rw [liftBVars_eq_rename, liftBVars_eq_rename, decompose_renameOuter] at repInner
    exact repInner.unrename (shiftAbove_injective 0 owned)
      (fun pattern _ => by simp only [liftBVars_eq_rename]) (insideLoc_locVariables isLoc count _) rfl rfl
  -- the copy reads canonically as the argument
  have copyAtomic : (Prenex.mk owned copyParts).Atomic locatedBlock := by
    intro component member
    exact ComponentKind.decompose_atom (reorderedWell.kinds component (List.mem_append_right _ member))
  have copyUsed : (Prenex.mk owned copyParts).Used := by
    intro index below
    have listedIndex : index < group.restrictions.length := below
    have listed : group.restrictions[index] ∈ group.restrictions := List.getElem_mem listedIndex
    obtain ⟨original, inGroup, freeHere⟩ := covered _ listed
    refine ⟨rename (Prenex.permute count order) original, List.mem_map.mpr ⟨original, inGroup, rfl⟩, ?_⟩
    have moved : Prenex.permute count order group.restrictions[index] = index := by
      rw [ownedMoved _ listed, List.Nodup.idxOf_getElem ownedNodup]
    exact (mentions_iff _ index).mpr ((freeIn_rename original).mpr ⟨_, freeHere, moved⟩)
  have copyDecomposed : Mettapedia.GSLT.LanguageDef.RestrictionBlocks.decompose locatedBlock
      (copyOf locatedBlock count group) = ⟨owned, copyParts⟩ :=
    decompose_toPattern copyAtomic copyUsed
  have fresh : locatedRepBlock.replicate ∉ locatedRepBlock.emptyUnits := by decide
  have restrictFresh : locatedRepBlock.replicate ≠ locatedRepBlock.restrict := by decide
  have sameNormal : normal locatedRepBlock ⟨owned, copyParts⟩ =
      normal locatedRepBlock (Mettapedia.GSLT.LanguageDef.RestrictionBlocks.decompose locatedBlock argumentLow) := by
    have decomposed := congrArg (Mettapedia.GSLT.LanguageDef.RestrictionBlocks.decompose locatedBlock) copied
    rw [decompose_canonicalOf fresh restrictFresh, decompose_canonicalOf fresh restrictFresh] at decomposed
    rw [← copyDecomposed]
    exact decomposed
  -- weights
  have keptWeight : 1 ≤ sizeList kept := by
    have repWeight := size_le_sizeList repKept
    have positive := size_pos (Pattern.apply "LRep" [argument])
    omega
  have componentsWeight : sizeList components = sizeList group.components + sizeList kept := by
    rw [sizeList_perm split, sizeList_append]
  have copyLighter : (Prenex.mk owned copyParts).mass < (Prenex.mk count components).mass := by
    simp only [Prenex.mass]
    rw [copyPartsIs, sizeList_map_rename, componentsWeight]
    omega
  have argumentLighter :
      (Mettapedia.GSLT.LanguageDef.RestrictionBlocks.decompose locatedBlock argumentLow).mass <
        (Prenex.mk count components).mass := by
    have decomposed := mass_decompose (block := locatedBlock) argumentLow
    have sized : size argumentLow = size argument := size_rename argument _
    have repWeight := size_le_sizeList repKept
    simp only [size, sizeList] at repWeight
    have formWeight : sizeList components ≤ (Prenex.mk count components).mass := by simp [Prenex.mass]
    rw [componentsWeight] at formWeight
    omega
  obtain ⟨argumentMembers, -⟩ := decompose_sound (language := locatedCalc) (block := locatedBlock)
    (rep_inv (keptLowMembers _ repLow))
  obtain ⟨homeIndex, homeBvar⟩ : ∃ homeIndex, home = .bvar homeIndex := ⟨_, by rw [homeIs, rename_bvar]⟩
  set least := 3 * ((Prenex.mk owned copyParts).mass +
    (Mettapedia.GSLT.LanguageDef.RestrictionBlocks.decompose locatedBlock argumentLow).mass +
    (normal locatedRepBlock ⟨owned, copyParts⟩).mass) + 3 with leastIs
  have copyEquiv : ∀ fuel, least ≤ fuel → ProcEquiv ambientCoreCalc ambientBlock free
      (List.replicate others.length nameType ++ bound)
      (Prenex.restricts ambientBlock owned
        (Prenex.body ambientBlock (readPlaced (fuel + 2) (liftBVars 0 owned home) copyParts)))
      (Prenex.toPattern ambientBlock
        (decodeForm fuel home (Mettapedia.GSLT.LanguageDef.RestrictionBlocks.decompose locatedBlock argumentLow))) := by
    intro fuel enough
    rw [homeBvar] at copyWell argumentWell ⊢
    have narrowContext := context.replicate others.length "Name"
    have copySide := (normalBelow ⟨owned, copyParts⟩ copyLighter copyWell copyLocVariables narrowContext
      copyMembers).2 (fuel + 3) (by omega) (by omega)
    have argumentSide := (normalBelow _ argumentLighter argumentWell copyLocVariables narrowContext
      argumentMembers).2 (fuel + 3) (by omega) (by rw [← sameNormal]; omega)
    rw [← sameNormal] at argumentSide
    rw [decodeForm_settled (.bvar homeIndex)
      (Mettapedia.GSLT.LanguageDef.RestrictionBlocks.decompose locatedBlock argumentLow)
      (first := fuel + 3) (second := fuel) (by omega) (by omega)] at argumentSide
    exact .trans _ _ _ (Relation.EqvGen.symm _ _ copySide) argumentSide
  -- the absorption
  refine ⟨least + 3 + 2 * kept.length, fun fuel enough => ?_⟩
  obtain ⟨fuel, rfl⟩ : ∃ fuel', fuel = fuel' + 1 := ⟨fuel - 1, by omega⟩
  have permuted := decode_perm (free := free) fuel (.bvar outer) (split.trans List.perm_append_comm) members
  have narrowed := decode_narrow (free := free) fuel (.bvar outer) ownedNodup ownedInside permutedMembers apart
  have top : ∀ component ∈ keptLow, childOf component ≠ some (liftBVars 0 others.length (.bvar outer)) := by
    intro component member isChild
    obtain ⟨index, below, same⟩ := childOf_bvar_of_kind (keptLowWell.kinds component member) isChild
    change index < others.length at below
    simp only [liftBVars, Nat.zero_le, if_true, Pattern.bvar.injEq] at same
    omega
  have core := absorb_core copyMembers copyPlaced copyChildren copyEquiv fuel keptLowMembers repLow homePlace top
    keptLowWell.unique_any (fun component member name isName => (keptLowWell.names component member name isName).1)
    (by rw [keptLowIs, List.length_map]; omega)
  have dropped := decode_drop (free := free) fuel (.bvar outer) ownedNodup ownedInside keptMembers apart
  exact .trans _ _ _ permuted (.trans _ _ _ narrowed (.trans _ _ _
    (restricts_congr (language := ambientCoreCalc) (block := ambientBlock) others.length core) dropped))

end Mettapedia.Languages.ProcessCalculi.Ambient.Decoding
