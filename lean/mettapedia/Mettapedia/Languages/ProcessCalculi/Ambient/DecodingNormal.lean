import Mettapedia.Languages.ProcessCalculi.Ambient.DecodingBlocks

/-!
# Reading back reordered and re-read components

Normalizing a block reorders its components and reads every component's own blocks again. Read back, both change
the reading only up to the ambient laws:

- **reordered components** read as the same processes in another order at every place (`readPlaced_perm`);
- **components changed one by one**, each keeping its place and its marker's location and reading its own blocks
  equivalently, read equivalently at every place (`readPlaced_map`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.Ambient.Decoding

open Mettapedia.Languages.ProcessCalculi.Ambient.Comm (ambientCoreCalc)

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.GSLT.LanguageDef.RestrictionBlocks (Prenex Members ProcEquiv body_typed body_congr
  body_perm_equivalent IsOrder rename rename_comp liftBVars_eq_rename shiftAbove permute_injective permute_of_ge
  block_reorder_equivalent orders_reorders orders_complete mentions mentions_iff freeIn_rename rename_congr
  drop_unused_equivalent outsideOf outsideOf_unused mem_outsideOf)
open Mettapedia.OSLF.MeTTaIL.CanonicalBags (FreeIn)
open Mettapedia.OSLF.MeTTaIL.Substitution (liftBVars)
open Mettapedia.Languages.ProcessCalculi.Ambient.Full (ambientBlock amb_fill)
open Mettapedia.Languages.ProcessCalculi.Ambient.Located (locatedCalc locatedBlock)
open Mettapedia.Languages.ProcessCalculi.Ambient.Encoding (nameType procType)

variable {free : FreeTypeContext}

/-- Two maps of one list are related member by member when their images of each member are. -/
theorem forall₂_map_map {α β : Type} {relation : β → β → Prop} {first second : α → β} :
    ∀ {list : List α}, (∀ element ∈ list, relation (first element) (second element)) →
      List.Forall₂ relation (list.map first) (list.map second)
  | [], _ => .nil
  | element :: _, related =>
      .cons (related element List.mem_cons_self)
        (forall₂_map_map fun other member => related other (List.mem_cons_of_mem _ member))

/-- The readings of typed located components are typed. -/
theorem readPlaced_members {bound : List TypeExpr} (fuel : Nat) (place : Pattern) {components : List Pattern}
    (members : Members locatedCalc locatedBlock free bound components) :
    Members ambientCoreCalc ambientBlock free bound (readPlaced fuel place components) :=
  (decode_typed fuel).2.1 place components members

/-- **A marker's content, read, is filled with an equivalent content.** -/
theorem wrapContent_fill {bound : List TypeExpr} (label : String) {name first second : Pattern}
    (nameTyped : HasType ambientCoreCalc free bound name nameType)
    (equivalent : ProcEquiv ambientCoreCalc ambientBlock free bound first second) :
    ProcEquiv ambientCoreCalc ambientBlock free bound (wrapContent label name first) (wrapContent label name second) := by
  unfold wrapContent
  split_ifs
  · exact amb_fill nameTyped equivalent
  · exact equivalent

/-- **A component read among equivalent surroundings reads equivalently**: a marker's ambient, around equivalent
contents; any other component, as it is. -/
theorem readComponent_equivalent {bound : List TypeExpr} {fuel : Nat} {place component : Pattern}
    {first second : List Pattern} (typed : HasType locatedCalc free bound component procType)
    (children : ∀ child, childOf component = some child →
      ProcEquiv ambientCoreCalc ambientBlock free bound (Prenex.body ambientBlock (readPlaced fuel child first))
        (Prenex.body ambientBlock (readPlaced fuel child second))) :
    ProcEquiv ambientCoreCalc ambientBlock free bound (readComponent (fuel + 1) place component first)
      (readComponent (fuel + 1) place component second) := by
  cases component with
  | apply label arguments =>
      match arguments, typed, children with
      | [_, child, third], typed, children =>
          simp only [readComponent]
          split_ifs with isMarker isName
          · rcases triple_inv typed with ⟨-, -, nameTyped⟩ | ⟨listed, -, -⟩ | ⟨rfl, -, -⟩
            · exact wrapContent_fill label (variable_typed nameTyped isName)
                (children child (by simp [childOf, isMarker]))
            · exact absurd listed (not_capability_of_marker isMarker)
            · simp [markers] at isMarker
          all_goals exact .refl _
      | [], _, _ => exact .refl _
      | [_], _, _ => exact .refl _
      | [_, _], _, _ => exact .refl _
      | _ :: _ :: _ :: _ :: _, _, _ => exact .refl _
  | _ => exact .refl _

/-- **Reordered components read as reordered processes**, at every place. -/
theorem readPlaced_perm : ∀ (fuel : Nat) {bound : List TypeExpr} {first second : List Pattern} (place : Pattern),
    first.Perm second → Members locatedCalc locatedBlock free bound first →
    ProcEquiv ambientCoreCalc ambientBlock free bound (Prenex.body ambientBlock (readPlaced fuel place first))
      (Prenex.body ambientBlock (readPlaced fuel place second))
  | 0, _, _, _, _, _, _ => .refl _
  | fuel + 1, bound, first, second, place, permutation, members => by
      have secondMembers : Members locatedCalc locatedBlock free bound second :=
        fun element member => members element (permutation.symm.subset member)
      have restMembers : ∀ {list : List Pattern}, Members locatedCalc locatedBlock free bound list →
          Members locatedCalc locatedBlock free bound (list.filter fun other => !placedAt place other) :=
        fun listMembers element member => listMembers element (List.mem_filter.mp member).1
      rw [readPlaced_succ, readPlaced_succ]
      -- first reorder the components placed here, then read each among the reordered others
      have hereMembers := readPlaced_members (fuel + 1) place members
      rw [readPlaced_succ] at hereMembers
      refine .trans _ _ _ (body_perm_equivalent hereMembers ((permutation.filter _).map _)) ?_
      refine body_congr (fun element member => ?_) (forall₂_map_map fun component inFiltered => ?_)
      · obtain ⟨original, inFiltered, rfl⟩ := List.mem_map.mp member
        exact (decode_typed fuel).2.2 place original _ (secondMembers original (List.mem_filter.mp inFiltered).1)
          (restMembers members)
      · cases fuel with
        | zero => exact .refl _
        | succ fuel =>
            exact readComponent_equivalent (secondMembers component (List.mem_filter.mp inFiltered).1)
              fun child _ => readPlaced_perm fuel child (permutation.filter _) (restMembers members)

theorem filter_map_placed {change : Pattern → Pattern} {components : List Pattern} (place : Pattern) (keep : Bool → Bool)
    (keepsPlace : ∀ component ∈ components, placeAt (change component) = placeAt component) :
    (components.map change).filter (fun component => keep (placedAt place component)) =
      (components.filter fun component => keep (placedAt place component)).map change := by
  rw [List.filter_map]
  congr 1
  exact List.filter_congr fun component member => by simp [Function.comp, placedAt, keepsPlace component member]

/-- **Components changed one by one read equivalently**: a change that keeps every component's place and its marker's
location, and reads every component equivalently among equivalent surroundings, reads equivalently at every place. -/
theorem readPlaced_map {change : Pattern → Pattern} : ∀ (fuel : Nat) {bound : List TypeExpr}
    {components : List Pattern} (place : Pattern),
    Members locatedCalc locatedBlock free bound components →
    Members locatedCalc locatedBlock free bound (components.map change) →
    (∀ component ∈ components, placeAt (change component) = placeAt component) →
    (∀ component ∈ components, ∀ (fuel' : Nat) (place' : Pattern) (first second : List Pattern),
      Members locatedCalc locatedBlock free bound first → Members locatedCalc locatedBlock free bound second →
      (∀ child, childOf component = some child →
        ProcEquiv ambientCoreCalc ambientBlock free bound (Prenex.body ambientBlock (readPlaced fuel' child first))
          (Prenex.body ambientBlock (readPlaced fuel' child second))) →
      ProcEquiv ambientCoreCalc ambientBlock free bound (readComponent (fuel' + 1) place' (change component) first)
        (readComponent (fuel' + 1) place' component second)) →
    ProcEquiv ambientCoreCalc ambientBlock free bound
      (Prenex.body ambientBlock (readPlaced fuel place (components.map change)))
      (Prenex.body ambientBlock (readPlaced fuel place components))
  | 0, _, _, _, _, _, _, _ => .refl _
  | fuel + 1, bound, components, place, members, changedMembers, keepsPlace, reads => by
      rw [readPlaced_succ, readPlaced_succ]
      have here := filter_map_placed place id keepsPlace
      have elsewhere := filter_map_placed place (fun placed => !placed) keepsPlace
      simp only [id] at here elsewhere
      rw [here, elsewhere, List.map_map]
      have restMembers : Members locatedCalc locatedBlock free bound
          (components.filter fun other => !placedAt place other) :=
        fun element member => members element (List.mem_filter.mp member).1
      have changedRestMembers : Members locatedCalc locatedBlock free bound
          ((components.filter fun other => !placedAt place other).map change) := by
        intro element member
        obtain ⟨original, inRest, rfl⟩ := List.mem_map.mp member
        exact changedMembers _ (List.mem_map.mpr ⟨original, (List.mem_filter.mp inRest).1, rfl⟩)
      have firstMembers := readPlaced_members (fuel + 1) place changedMembers
      rw [readPlaced_succ, here, elsewhere, List.map_map] at firstMembers
      refine body_congr firstMembers (forall₂_map_map fun component inFiltered => ?_)
      have inComponents := (List.mem_filter.mp inFiltered).1
      cases fuel with
      | zero => exact .refl _
      | succ fuel =>
          exact reads component inComponents fuel place _ _ changedRestMembers restMembers fun child _ =>
            readPlaced_map fuel child restMembers changedRestMembers
              (fun other member => keepsPlace other (List.mem_filter.mp member).1)
              (fun other member => reads other (List.mem_filter.mp member).1)

/-! ## Reordering a block's restrictions -/

/-- A reordering of a block's restrictions leaves the place read inside the block. -/
theorem permute_lift (count : Nat) (order : List Nat) (place : Pattern) :
    rename (Prenex.permute count order) (liftBVars 0 count place) = liftBVars 0 count place := by
  rw [liftBVars_eq_rename, rename_comp]
  congr 1
  funext index
  simp only [Function.comp, shiftAbove, Nat.not_lt_zero, if_false]
  exact permute_of_ge order (by omega)

/-- **A block with its restrictions reordered reads back equivalently.** -/
theorem decode_reorder {bound : List TypeExpr} (fuel : Nat) (place : Pattern) {count : Nat} {order : List Nat}
    (isOrder : IsOrder count order) {components : List Pattern}
    (members : Members locatedCalc locatedBlock free (List.replicate count nameType ++ bound) components) :
    ProcEquiv ambientCoreCalc ambientBlock free bound
      (Prenex.toPattern ambientBlock
        (decodeForm (fuel + 1) place ⟨count, components.map (rename (Prenex.permute count order))⟩))
      (Prenex.toPattern ambientBlock (decodeForm (fuel + 1) place ⟨count, components⟩)) := by
  have renamed := (decode_rename fuel (permute_injective isOrder)).2.1 (liftBVars 0 count place) components
  rw [permute_lift] at renamed
  simp only [decodeForm]
  rw [renamed]
  have itemsMembers := readPlaced_members (bound := List.replicate count nameType ++ bound) fuel
    (liftBVars 0 count place) members
  exact Relation.EqvGen.symm _ _ (block_reorder_equivalent (language := ambientCoreCalc) (block := ambientBlock)
    (orders_reorders _ order (orders_complete _ _ isOrder)) itemsMembers).2

/-! ## Dropping unused restrictions -/

/-- **Kept restrictions back in place**: the inverse of renumbering a block's kept restrictions. -/
def ungroup (count : Nat) (kept : List Nat) (index : Nat) : Nat :=
  if index < kept.length then kept.getD index 0 else index - kept.length + count

section Ungroup

variable {count : Nat} {kept : List Nat}

theorem ungroup_injective (nodup : kept.Nodup) (inside : ∀ index ∈ kept, index < count) :
    Function.Injective (ungroup count kept) := by
  intro first second same
  simp only [ungroup] at same
  have getBelow : ∀ {index : Nat}, index < kept.length → kept.getD index 0 < count := fun below => by
    rw [List.getD_eq_getElem _ _ below]
    exact inside _ (List.getElem_mem below)
  split_ifs at same with firstBelow secondBelow secondBelow
  · rw [List.getD_eq_getElem _ _ firstBelow, List.getD_eq_getElem _ _ secondBelow] at same
    exact (List.Nodup.getElem_inj_iff nodup).mp same
  · have := getBelow firstBelow; omega
  · have := getBelow secondBelow; omega
  · omega

theorem groupIndex_ungroup (nodup : kept.Nodup) (inside : ∀ index ∈ kept, index < count) (index : Nat) :
    Prenex.groupIndex count kept (ungroup count kept index) = index := by
  simp only [ungroup, Prenex.groupIndex]
  split_ifs with below inRange inRange
  · rw [List.getD_eq_getElem _ _ below, List.Nodup.idxOf_getElem nodup]
  · rw [List.getD_eq_getElem _ _ below] at inRange
    exact absurd (inside _ (List.getElem_mem below)) inRange
  · omega
  · omega

theorem ungroup_groupIndex {index : Nat} (kept_or_outside : index ∈ kept ∨ count ≤ index)
    (inside : ∀ index ∈ kept, index < count) :
    ungroup count kept (Prenex.groupIndex count kept index) = index := by
  simp only [ungroup, Prenex.groupIndex]
  rcases kept_or_outside with member | outside
  · have below := inside index member
    simp only [below, if_true, List.idxOf_lt_length_iff.mpr member]
    rw [List.getD_eq_getElem _ _ (List.idxOf_lt_length_iff.mpr member), List.getElem_idxOf]
  · have notBelow : ¬ index < count := by omega
    simp only [notBelow, if_false]
    split_ifs <;> omega

/-- **Renumbering a block's kept restrictions and putting them back is nothing**, for components using only those. -/
theorem ungroup_restores (inside : ∀ index ∈ kept, index < count) {components : List Pattern}
    (uses : ∀ component ∈ components, ∀ index, FreeIn index component → index < count → index ∈ kept) :
    (components.map (rename (Prenex.groupIndex count kept))).map (rename (ungroup count kept)) = components := by
  rw [List.map_map]
  conv_rhs => rw [← List.map_id components]
  refine List.map_congr_left fun component member => ?_
  simp only [Function.comp, id]
  rw [rename_comp]
  conv_rhs => rw [← Mettapedia.GSLT.LanguageDef.RestrictionBlocks.rename_id component]
  apply rename_congr
  intro index free
  by_cases below : index < count
  · exact ungroup_groupIndex (.inl (uses component member index free below)) inside
  · exact ungroup_groupIndex (.inr (by omega)) inside

end Ungroup

/-- **A block with some unused restrictions dropped reads back equivalently**, the others renumbered in their order. -/
theorem decode_drop {bound : List TypeExpr} (fuel : Nat) (place : Pattern) {count : Nat} {unused : List Nat}
    (unusedNodup : unused.Nodup) (unusedInside : ∀ index ∈ unused, index < count) {components : List Pattern}
    (members : Members locatedCalc locatedBlock free (List.replicate count nameType ++ bound) components)
    (apart : ∀ component ∈ components, ∀ index ∈ unused, ¬ FreeIn index component) :
    ProcEquiv ambientCoreCalc ambientBlock free bound
      (Prenex.toPattern ambientBlock (decodeForm (fuel + 1) place ⟨(outsideOf count unused).length,
        components.map (rename (Prenex.groupIndex count (outsideOf count unused)))⟩))
      (Prenex.toPattern ambientBlock (decodeForm (fuel + 1) place ⟨count, components⟩)) := by
  set kept := outsideOf count unused with keptIs
  have nodup : kept.Nodup := List.nodup_range.filter _
  have inside : ∀ index ∈ kept, index < count := fun index member => (mem_outsideOf.mp member).1
  have injective := ungroup_injective nodup inside
  -- the block is its narrowed block with the kept restrictions back in place
  have restored : (components.map (rename (Prenex.groupIndex count kept))).map (rename (ungroup count kept)) =
      components := ungroup_restores inside fun component member index free below =>
    mem_outsideOf.mpr ⟨below, fun listed => apart component member index listed free⟩
  have placeRestored : rename (ungroup count kept) (liftBVars 0 kept.length place) = liftBVars 0 count place := by
    rw [liftBVars_eq_rename, liftBVars_eq_rename, rename_comp]
    congr 1
    funext index
    simp only [Function.comp, shiftAbove, Nat.not_lt_zero, if_false, ungroup]
    split_ifs <;> omega
  have renamed := (decode_rename fuel injective).2.1 (liftBVars 0 kept.length place)
    (components.map (rename (Prenex.groupIndex count kept)))
  rw [placeRestored, restored] at renamed
  simp only [decodeForm]
  rw [renamed]
  -- the restored reading drops the unused restrictions back
  obtain ⟨keptMembers, -⟩ := drop_unused_equivalent (language := locatedCalc)
    (block := Mettapedia.Languages.ProcessCalculi.Ambient.Located.locatedRepBlock) unusedNodup unusedInside members
    apart
  have itemsMembers := readPlaced_members (bound := List.replicate kept.length nameType ++ bound) fuel
    (liftBVars 0 kept.length place) keptMembers
  set items := readPlaced fuel (liftBVars 0 kept.length place) (components.map (rename (Prenex.groupIndex count kept)))
  have restoredMembers : Members ambientCoreCalc ambientBlock free (List.replicate count nameType ++ bound)
      (items.map (rename (ungroup count kept))) := by
    intro element member
    obtain ⟨original, inItems, rfl⟩ := List.mem_map.mp member
    exact Mettapedia.GSLT.LanguageDef.RestrictionBlocks.rename_typed (itemsMembers original inItems)
      fun index sort lookup => by
        simp only [ungroup]
        split_ifs with below
        · rw [List.getD_eq_getElem _ _ below]
          have keptBelow := inside _ (List.getElem_mem below)
          rw [List.getElem?_append_left (by simpa using below), List.getElem?_replicate] at lookup
          rw [List.getElem?_append_left (by simpa using keptBelow), List.getElem?_replicate]
          simpa [below, keptBelow] using lookup
        · rw [List.getElem?_append_right (by simp only [List.length_replicate]; omega)] at lookup
          rw [List.getElem?_append_right (by simp only [List.length_replicate]; omega)]
          simpa [show index - kept.length + count - count = index - kept.length by omega] using lookup
  have dropped := drop_unused_equivalent (language := ambientCoreCalc)
    (block := Mettapedia.Languages.ProcessCalculi.Ambient.Full.ambientRepBlock) unusedNodup unusedInside
    restoredMembers (by
      intro element member index listed free
      obtain ⟨original, -, rfl⟩ := List.mem_map.mp member
      obtain ⟨source, -, image⟩ := (freeIn_rename original).mp free
      simp only [ungroup] at image
      split_ifs at image with below
      · rw [List.getD_eq_getElem _ _ below] at image
        have keptMember : kept[source] ∈ kept := List.getElem_mem below
        rw [image] at keptMember
        exact (mem_outsideOf.mp keptMember).2 listed
      · have := unusedInside index listed
        omega)
  rw [← keptIs, List.map_map] at dropped
  have back : (rename (Prenex.groupIndex count kept) ∘ rename (ungroup count kept)) = id := by
    funext item
    simp only [Function.comp, id, rename_comp]
    conv_rhs => rw [← Mettapedia.GSLT.LanguageDef.RestrictionBlocks.rename_id item]
    congr 1
    funext index
    exact groupIndex_ungroup nodup inside index
  rw [back, List.map_id] at dropped
  exact Relation.EqvGen.symm _ _ dropped.2

/-- **A block with its unused restrictions dropped reads back equivalently.** -/
theorem decode_prune {bound : List TypeExpr} (fuel : Nat) (place : Pattern) {form : Prenex}
    (members : Members locatedCalc locatedBlock free (List.replicate form.count nameType ++ bound) form.components) :
    ProcEquiv ambientCoreCalc ambientBlock free bound
      (Prenex.toPattern ambientBlock (decodeForm (fuel + 1) place form.prune))
      (Prenex.toPattern ambientBlock (decodeForm (fuel + 1) place form)) := by
  obtain ⟨count, components⟩ := form
  have dropped := decode_drop (free := free) fuel place (unused := (List.range count).filter fun index =>
      !components.any (mentions index)) (List.nodup_range.filter _)
    (fun index member => List.mem_range.mp (List.mem_filter.mp member).1) members (by
      intro component inComponents index listed freeHere
      have unused := (List.mem_filter.mp listed).2
      simp only [Bool.not_eq_true', List.any_eq_false] at unused
      exact absurd ((mentions_iff component index).mpr freeHere) (by simp [unused component inComponents]))
  rw [outsideOf_unused] at dropped
  exact dropped

end Mettapedia.Languages.ProcessCalculi.Ambient.Decoding
