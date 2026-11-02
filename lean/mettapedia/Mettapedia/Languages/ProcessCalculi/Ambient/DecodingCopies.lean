import Mettapedia.Languages.ProcessCalculi.Ambient.DecodingAbsorb

/-!
# Where a copy group sits and what it places

A group of a well-located block's components that is a copy of a replicated component's argument, owning the
restrictions it uses that the replicated component does not, and sharing none of them with the rest of the block:

- sits where the replicated component sits, or at its own restrictions (`copy_places`);
- places its ambients only at its own restrictions (`copy_children`): a marker of the group placing an ambient at
  another location would place it at the replicated component's own location, whose ambient would then sit, through
  markers of the group only, inside itself, which nested locations rule out.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.Ambient.Decoding

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Substitution (liftBVars)
open Mettapedia.OSLF.MeTTaIL.CanonicalBags (FreeIn freeIn_bvar freeIn_apply)
open Mettapedia.GSLT.LanguageDef.RestrictionBlocks (Prenex decompose mentions mentions_iff Group copyOf outsideOf
  canonicalOf rename)
open Mettapedia.Languages.ProcessCalculi.Ambient.Located (locatedBlock locatedRepBlock)

/-- A marker uses the location it places its ambient at. -/
theorem freeIn_child {component : Pattern} {index : Nat} (isChild : childOf component = some (.bvar index)) :
    FreeIn index component := by
  obtain ⟨label, parent, name, -, rfl⟩ := childOf_eq_some isChild
  exact freeIn_apply.mpr ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, .bvar index⟩

/-- **A marked restriction the replicated component uses is its place**: its argument uses from outside only its
place among the locations. -/
theorem rep_location {isLoc : Pattern → Prop} {place : Pattern} {count : Nat} {components : List Pattern}
    (well : WellLocated isLoc place ⟨count, components⟩) {argument at' : Pattern}
    (repMember : Pattern.apply "LRep" [argument] ∈ components)
    (repPlace : placeAt (.apply "LRep" [argument]) = some at') {index : Nat} (below : index < count)
    (marked : Marked components index) (mentioned : mentions index (.apply "LRep" [argument]) = true) :
    Pattern.bvar index = at' := by
  have argumentUses : FreeIn index argument := by
    obtain ⟨inner, member, free⟩ := freeIn_apply.mp ((mentions_iff _ index).mp mentioned)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    subst member
    exact free
  have argumentWell := match well with
    | .intro _ _ _ _ _ _ reps _ _ _ _ _ => reps _ repMember argument at' rfl repPlace
  obtain ⟨inner, innerMember, innerFree⟩ :=
    (Mettapedia.GSLT.LanguageDef.RestrictionBlocks.freeIn_decompose (block := locatedBlock) argument index).mp
      argumentUses
  rcases argumentWell.freeIn_outer (insideLoc_locVariables isLoc count components) inner innerMember _ innerFree
      (Nat.le_add_left _ _) with same | apart
  · simpa using same
  · exfalso
    apply apart
    simp only [Nat.add_sub_cancel, insideLoc, below, if_true]
    exact marked

section Copy

variable {isLoc : Pattern → Prop} {outer count : Nat} {components : List Pattern}
  {argument at' : Pattern} {group : Group} {kept : List Pattern}

/-- **A copy group sits at its replicated component's place or at its own restrictions.** -/
theorem copy_places (well : WellLocated isLoc (.bvar outer) ⟨count, components⟩)
    (repMember : Pattern.apply "LRep" [argument] ∈ components)
    (repPlace : placeAt (.apply "LRep" [argument]) = some at')
    (inComponents : ∀ component ∈ group.components, component ∈ components)
    (ownedNodup : group.restrictions.Nodup) (ownedInside : ∀ index ∈ group.restrictions, index < count)
    (allowedOnly : ∀ index ∈ group.restrictions, mentions index (.apply "LRep" [argument]) = false)
    (covers : ∀ component ∈ group.components, ∀ index < count, FreeIn index component →
      mentions index (.apply "LRep" [argument]) = false → index ∈ group.restrictions)
    (copied : canonicalOf locatedRepBlock (copyOf locatedBlock count group) =
      canonicalOf locatedRepBlock (rename (Prenex.groupIndex count (outsideOf count group.restrictions)) argument)) :
    ∀ component ∈ group.components, ∀ spot, placeAt component = some spot →
      spot = at' ∨ ∃ index ∈ group.restrictions, spot = .bvar index := by
  intro component member spot isPlaced
  rcases well.placed component (inComponents component member) spot isPlaced with atPlace | ⟨index, below, rfl, -⟩
  · have lifted : liftBVars 0 count (.bvar outer) = .bvar (outer + count) := by simp [liftBVars]
    simp only at atPlace
    rw [atPlace, lifted] at isPlaced ⊢
    exact .inl (copy_placed_outer well repMember repPlace ownedNodup ownedInside allowedOnly member isPlaced copied)
  · by_cases owned : index ∈ group.restrictions
    · exact .inr ⟨index, owned, rfl⟩
    · exact .inl (copy_placed_binder well repMember repPlace covers member (inComponents component member) below
        isPlaced owned)

/-- **A copy group places its ambients at its own restrictions only.** -/
theorem copy_children (well : WellLocated isLoc (.bvar outer) ⟨count, components⟩)
    (repMember : Pattern.apply "LRep" [argument] ∈ components)
    (repPlace : placeAt (.apply "LRep" [argument]) = some at')
    (split : components.Perm (group.components ++ kept))
    (apart : ∀ component ∈ kept, ∀ index ∈ group.restrictions, ¬ FreeIn index component)
    (ownedNodup : group.restrictions.Nodup) (ownedInside : ∀ index ∈ group.restrictions, index < count)
    (allowedOnly : ∀ index ∈ group.restrictions, mentions index (.apply "LRep" [argument]) = false)
    (covers : ∀ component ∈ group.components, ∀ index < count, FreeIn index component →
      mentions index (.apply "LRep" [argument]) = false → index ∈ group.restrictions)
    (copied : canonicalOf locatedRepBlock (copyOf locatedBlock count group) =
      canonicalOf locatedRepBlock (rename (Prenex.groupIndex count (outsideOf count group.restrictions)) argument)) :
    ∀ component ∈ group.components, ∀ child, childOf component = some child →
      ∃ index ∈ group.restrictions, child = .bvar index := by
  have inComponents : ∀ component ∈ group.components, component ∈ components :=
    fun component member => split.symm.subset (List.mem_append_left _ member)
  have places := copy_places well repMember repPlace inComponents ownedNodup ownedInside allowedOnly covers copied
  have markerInGroup : ∀ marker ∈ components, ∀ index ∈ group.restrictions,
      childOf marker = some (.bvar index) → marker ∈ group.components := by
    intro marker member index owned isChild
    rcases List.mem_append.mp (split.subset member) with inGroup | inKept
    · exact inGroup
    · exact absurd (freeIn_child isChild) (apart marker inKept index owned)
  intro component member child isChild
  obtain ⟨index, below, rfl⟩ := childOf_bvar_of_kind (well.kinds component (inComponents component member)) isChild
  change index < count at below
  by_cases owned : index ∈ group.restrictions
  · exact ⟨index, owned, rfl⟩
  exfalso
  have mentioned : mentions index (.apply "LRep" [argument]) = true := by
    by_contra unmentioned
    exact owned (covers component member index below (freeIn_child isChild) (by simpa using unmentioned))
  have atIs : Pattern.bvar index = at' :=
    rep_location well repMember repPlace below ⟨component, inComponents component member, isChild⟩ mentioned
  obtain ⟨depth, grows⟩ := well.nested
  -- every location of the replicated component's place or owned and marked has a marker of the group sitting at
  -- another such location, less deep
  have descends : ∀ location, location < count → (location = index ∨ (location ∈ group.restrictions ∧
      Marked components location)) → ∃ above, above < count ∧ (above = index ∨ (above ∈ group.restrictions ∧
        Marked components above)) ∧ depth above < depth location := by
    intro location locationBelow inSet
    obtain ⟨marker, markerMember, markerGroup, markerChild⟩ : ∃ marker ∈ components,
        marker ∈ group.components ∧ childOf marker = some (.bvar location) := by
      rcases inSet with rfl | ⟨locationOwned, marker, markerMember, markerChild⟩
      · exact ⟨component, inComponents component member, member, isChild⟩
      · exact ⟨marker, markerMember, markerInGroup marker markerMember location locationOwned markerChild,
          markerChild⟩
    obtain ⟨label, parent, name, isMarker, rfl⟩ := childOf_eq_some markerChild
    have markerPlace := placeAt_ofMarker isMarker parent (.bvar location) name
    rcases places _ markerGroup parent markerPlace with atRep | ⟨above, aboveOwned, rfl⟩
    · have sits : placeAt (Pattern.apply label [parent, .bvar location, name]) = some (.bvar index) := by
        rw [markerPlace, atRep, ← atIs]
      exact ⟨index, below, .inl rfl, grows _ markerMember index location below locationBelow sits markerChild⟩
    · have aboveBelow := ownedInside above aboveOwned
      have aboveMarked : Marked components above := by
        rcases well.placed _ markerMember _ markerPlace with atPlace | ⟨other, -, same, isMarked⟩
        · simp [liftBVars] at atPlace
          omega
        · simp only [Pattern.bvar.injEq] at same
          subst same
          exact isMarked
      exact ⟨above, aboveBelow, .inr ⟨aboveOwned, aboveMarked⟩,
        grows _ markerMember above location aboveBelow locationBelow markerPlace markerChild⟩
  have bottomless : ∀ depthValue, ∀ location, location < count → (location = index ∨
      (location ∈ group.restrictions ∧ Marked components location)) → depth location = depthValue → False := by
    intro depthValue
    induction depthValue using Nat.strong_induction_on with
    | _ depthValue recurse =>
        intro location locationBelow inSet depthIs
        obtain ⟨above, aboveBelow, aboveIn, smaller⟩ := descends location locationBelow inSet
        exact recurse (depth above) (by omega) above aboveBelow aboveIn rfl
  exact bottomless _ index below (.inl rfl) rfl

end Copy

end Mettapedia.Languages.ProcessCalculi.Ambient.Decoding
