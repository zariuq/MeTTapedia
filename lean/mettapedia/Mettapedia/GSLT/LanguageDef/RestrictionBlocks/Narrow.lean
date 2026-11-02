import Mettapedia.GSLT.LanguageDef.RestrictionBlocks.MoleculeSplit

/-!
# Narrowing the scope of restrictions a part uses alone

When restrictions `S` of a block are used only by one part of its components, they can be read as a block around
that part inside the rest of the block: the block is the rest's block holding the part's block among its components
(`narrow_equivalent`). The reordering is the split order with the part's restrictions innermost and every other
restriction next, so no restriction goes unused; the rest is read without `S` (`Prenex.groupIndex count others`), and
the part as a block of its own over `S` inside it (`copyOf`).
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.RestrictionBlocks

open Mettapedia.OSLF.MeTTaIL.Syntax

/-- The restrictions of a block of `count` outside a list of them, in increasing order. -/
def outsideOf (count : Nat) (restrictions : List Nat) : List Nat :=
  (List.range count).filter fun index => !restrictions.contains index

/-- **A group read as a copy inside the rest of its block**: the block's restrictions reordered so that the group's
come innermost, in their order, and the others next, as the rest of the block reads them. -/
def copyOf (block : Block) (count : Nat) (group : Group) : Pattern :=
  Prenex.toPattern block ⟨group.restrictions.length,
    group.components.map (rename (Prenex.permute count (splitOrder count (outsideOf count group.restrictions)
      group.restrictions)))⟩

open Mettapedia.OSLF.MeTTaIL.CanonicalBags (FreeIn)
open Mettapedia.OSLF.MeTTaIL.Substitution (liftBVars)

theorem mem_outsideOf {count : Nat} {restrictions : List Nat} {index : Nat} :
    index ∈ outsideOf count restrictions ↔ index < count ∧ index ∉ restrictions := by
  simp [outsideOf]

/-- **The restrictions outside a list, and the list, split a block with none unused.** -/
theorem outside_parts {count : Nat} {restrictions : List Nat} (nodup : restrictions.Nodup)
    (inside : ∀ index ∈ restrictions, index < count) :
    SplitParts count (outsideOf count restrictions) restrictions where
  firstNodup := List.nodup_range.filter _
  secondNodup := nodup
  firstInside := fun _ member => (mem_outsideOf.mp member).1
  secondInside := inside
  disjoint := fun _ member listed => (mem_outsideOf.mp member).2 listed

theorem outside_unused (count : Nat) (restrictions : List Nat) :
    unusedRestrictions count (outsideOf count restrictions) restrictions = [] := by
  rw [unusedRestrictions, List.filter_eq_nil_iff]
  intro index member
  have below := List.mem_range.mp member
  by_cases listed : index ∈ restrictions
  · simp [listed]
  · simp [mem_outsideOf.mpr ⟨below, listed⟩]

section Narrow

variable {language : LanguageDef} {block : Block} [laws : BlockSignature language block]

open Mettapedia.GSLT.LanguageDef.WellSorted (HasType FreeTypeContext)

/-- **The scope of restrictions a part uses alone narrows onto it**: the block of the part and the rest is the
rest's block, read without those restrictions, holding the part's block over them. -/
theorem narrow_equivalent {free : FreeTypeContext} {bound : List TypeExpr} {count : Nat}
    {restrictions : List Nat} (nodup : restrictions.Nodup) (inside : ∀ index ∈ restrictions, index < count)
    {part rest : List Pattern}
    (members : Members language block free (List.replicate count (TypeExpr.base block.name) ++ bound) (part ++ rest))
    (apart : ∀ component ∈ rest, ∀ index ∈ restrictions, ¬ FreeIn index component) :
    Members language block free
        (List.replicate (outsideOf count restrictions).length (TypeExpr.base block.name) ++ bound)
        (copyOf block count ⟨restrictions, part⟩ ::
          rest.map (rename (Prenex.groupIndex count (outsideOf count restrictions)))) ∧
      ProcEquiv language block free bound (Prenex.toPattern block ⟨count, part ++ rest⟩)
        (Prenex.toPattern block ⟨(outsideOf count restrictions).length,
          copyOf block count ⟨restrictions, part⟩ ::
            rest.map (rename (Prenex.groupIndex count (outsideOf count restrictions)))⟩) := by
  set others := outsideOf count restrictions with othersIs
  have parts := outside_parts nodup inside
  have total : restrictions.length + others.length = count := by
    have counted := parts.lengths
    rw [outside_unused, List.length_nil, Nat.add_zero] at counted
    exact counted
  have reorders : Reorders (List.range count) (splitOrder count others restrictions) :=
    orders_reorders (List.range count) _ (orders_complete _ _ parts.splitOrder_perm)
  obtain ⟨reordered, reorderEquivalent⟩ := block_reorder_equivalent reorders members
  set order := splitOrder count others restrictions
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
  set copyParts := part.map (rename (Prenex.permute count order))
  set restParts := rest.map (rename (Prenex.groupIndex count others))
  have copyMembers : Members language block free
      (List.replicate restrictions.length (TypeExpr.base block.name) ++
        (List.replicate others.length (TypeExpr.base block.name) ++ bound)) copyParts := by
    intro element member
    have typed := reordered element (by simp only [List.map_append]; exact List.mem_append_left _ member)
    rw [← List.append_assoc, ← List.replicate_add, total]
    exact typed
  have restMembers : Members language block free (List.replicate others.length (TypeExpr.base block.name) ++ bound)
      restParts := part_members (restrictions := others) (fun element member => members element
        (List.mem_append_right _ member)) restUses
  have liftedMembers : Members language block free
      (List.replicate restrictions.length (TypeExpr.base block.name) ++
        (List.replicate others.length (TypeExpr.base block.name) ++ bound))
      (restParts.map (liftBVars 0 restrictions.length)) := by
    simpa using restMembers.lift (List.replicate restrictions.length (TypeExpr.base block.name))
  -- the reordered block is the inner restrictions inside the outer ones
  have shape : Prenex.toPattern block ⟨count, (part ++ rest).map (rename (Prenex.permute count order))⟩ =
      Prenex.restricts block others.length (Prenex.restricts block restrictions.length
        (Prenex.body block (copyParts ++ restParts.map (liftBVars 0 restrictions.length)))) := by
    rw [List.map_append, lifted, Prenex.toPattern, restricts_add, show others.length + restrictions.length = count by omega]
  -- regroup the body: the copy's components as one body beside the rest
  have regroup : ProcEquiv language block free
      (List.replicate restrictions.length (TypeExpr.base block.name) ++
        (List.replicate others.length (TypeExpr.base block.name) ++ bound))
      (Prenex.body block (copyParts ++ restParts.map (liftBVars 0 restrictions.length)))
      (.collection .hashBag (Prenex.body block copyParts :: restParts.map (liftBVars 0 restrictions.length)) none) := by
    have whole := bag_body_equivalent (copyMembers.append liftedMembers)
    have paired := bag_pair_equivalent copyMembers liftedMembers
    have bodied := bag_body_equivalent copyMembers
    have filled := bag_fill (before := []) (after := [.collection .hashBag (restParts.map (liftBVars 0 restrictions.length)) none])
      (rest := none) Members.nil (Members.cons (bag_typed liftedMembers) Members.nil) bodied
    simp only [List.nil_append] at filled
    have consed := bag_cons_equivalent (body_typed copyMembers) liftedMembers
    exact .trans _ _ _ (.symm _ _ whole) (.trans _ _ _ (.symm _ _ paired) (.trans _ _ _ filled consed))
  -- narrow: extrusion read backwards
  have extruded := extrusions_equivalent restrictions.length (body_typed copyMembers) restMembers
  have narrowed : ProcEquiv language block free (List.replicate others.length (TypeExpr.base block.name) ++ bound)
      (Prenex.restricts block restrictions.length
        (Prenex.body block (copyParts ++ restParts.map (liftBVars 0 restrictions.length))))
      (.collection .hashBag (copyOf block count ⟨restrictions, part⟩ :: restParts) none) :=
    .trans _ _ _ (restricts_congr restrictions.length regroup) (.symm _ _ extruded)
  have outer := restricts_congr others.length narrowed
  have copyTyped : HasType language free (List.replicate others.length (TypeExpr.base block.name) ++ bound)
      (copyOf block count ⟨restrictions, part⟩) (.base block.proc) :=
    restricts_typed _ (body_typed copyMembers)
  have unbag := restricts_congr others.length (bag_body_equivalent (Members.cons copyTyped restMembers))
  rw [shape] at reorderEquivalent
  exact ⟨Members.cons copyTyped restMembers, .trans _ _ _ reorderEquivalent (.trans _ _ _ outer unbag)⟩

end Narrow

end Mettapedia.GSLT.LanguageDef.RestrictionBlocks
