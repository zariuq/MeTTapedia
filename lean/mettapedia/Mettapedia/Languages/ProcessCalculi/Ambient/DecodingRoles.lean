import Mettapedia.Languages.ProcessCalculi.Ambient.DecodingWell

/-!
# Where a copy sits

A component uses the place it sits at (`freeIn_placeAt`). In a well-located block, a group of components that is a copy
of a replicated component's argument sits where the replicated component sits, or at the group's own restrictions
(`copy_placed_binder`, `copy_placed_outer`): a place the group uses but does not own is either one the replicated component uses, hence its own
place, the only location its argument uses from outside; or the block's place, which the copy and the argument then
use alike, since canonical forms keep the variables they use.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.Ambient.Decoding

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Substitution (liftBVars)
open Mettapedia.OSLF.MeTTaIL.CanonicalBags (FreeIn freeIn_bvar freeIn_apply)
open Mettapedia.GSLT.LanguageDef.RestrictionBlocks (Prenex decompose mentions mentions_iff)
open Mettapedia.Languages.ProcessCalculi.Ambient.Located (locatedBlock)

/-- **A component uses the place it sits at.** -/
theorem freeIn_placeOf : ∀ (fuel : Nat),
    (∀ (component : Pattern) (index : Nat), placeOf fuel component = some (.bvar index) → FreeIn index component) ∧
    (∀ (form : Prenex) (index : Nat), outerPlace fuel form = some (.bvar index) → form.FreePast index)
  | 0 => ⟨fun _ _ found => by simp [placeOf] at found, fun _ _ found => by simp [outerPlace] at found⟩
  | fuel + 1 => by
      obtain ⟨componentsBelow, formsBelow⟩ := freeIn_placeOf fuel
      refine ⟨fun component index found => ?_, fun form index found => ?_⟩
      · cases component with
        | apply label arguments =>
            match arguments, found with
            | [place, _, _], found =>
                simp only [placeOf] at found
                split_ifs at found
                simp only [Option.some.injEq] at found
                subst found
                exact freeIn_apply.mpr ⟨_, List.mem_cons_self, .bvar index⟩
            | [argument], found =>
                simp only [placeOf] at found
                split_ifs at found
                exact freeIn_apply.mpr ⟨argument, List.mem_cons_self,
                  (Mettapedia.GSLT.LanguageDef.RestrictionBlocks.freeIn_decompose (block := locatedBlock) argument
                    index).mpr (formsBelow _ index found)⟩
            | [place, _], found =>
                simp only [placeOf] at found
                split_ifs at found
                simp only [Option.some.injEq] at found
                subst found
                exact freeIn_apply.mpr ⟨_, List.mem_cons_self, .bvar index⟩
            | [], found => simp [placeOf] at found
            | _ :: _ :: _ :: _ :: _, found => simp [placeOf] at found
        | _ => simp [placeOf] at found
      · obtain ⟨count, components⟩ := form
        simp only [outerPlace] at found
        obtain ⟨component, member, lowered⟩ := List.exists_of_findSome?_eq_some found
        cases placed : placeOf fuel component with
        | none => rw [placed] at lowered; cases lowered
        | some at' =>
            rw [placed, Option.bind_some] at lowered
            cases at' with
            | bvar inner =>
                simp only [lowerBy] at lowered
                split_ifs at lowered with above
                simp only [Option.some.injEq, Pattern.bvar.injEq] at lowered
                refine ⟨component, member, ?_⟩
                simp only
                rw [show index + count = inner by omega]
                exact componentsBelow component inner placed
            | fvar _ => simp [lowerBy] at lowered
            | _ => simp [lowerBy] at lowered

theorem freeIn_placeAt {component : Pattern} {index : Nat} (found : placeAt component = some (.bvar index)) :
    FreeIn index component :=
  (freeIn_placeOf _).1 component index found

open Mettapedia.GSLT.LanguageDef.RestrictionBlocks (Group)

/-- **A copy sits at its replicated component's place, at a restriction of the block it does not own**: a restriction
the group uses but does not own is one the replicated component uses, and its argument uses from outside only its
place among the locations. -/
theorem copy_placed_binder {isLoc : Pattern → Prop} {place : Pattern} {count : Nat} {components : List Pattern}
    (well : WellLocated isLoc place ⟨count, components⟩) {argument at' : Pattern}
    (repMember : Pattern.apply "LRep" [argument] ∈ components)
    (repPlace : placeAt (.apply "LRep" [argument]) = some at') {group : Group}
    (covers : ∀ component ∈ group.components, ∀ index < count, FreeIn index component →
      mentions index (.apply "LRep" [argument]) = false → index ∈ group.restrictions)
    {component : Pattern} (inGroup : component ∈ group.components) (inComponents : component ∈ components)
    {index : Nat} (below : index < count) (sits : placeAt component = some (.bvar index))
    (notOwn : index ∉ group.restrictions) :
    Pattern.bvar index = at' := by
  have uses : FreeIn index component := freeIn_placeAt sits
  -- the replicated component uses the restriction
  have mentioned : mentions index (.apply "LRep" [argument]) = true := by
    by_contra unmentioned
    exact notOwn (covers component inGroup index below uses (by simpa using unmentioned))
  have argumentUses : FreeIn index argument := by
    obtain ⟨inner, member, free⟩ := freeIn_apply.mp ((mentions_iff _ index).mp mentioned)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    subst member
    exact free
  -- the argument is well-located at the replicated component's place
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
    rcases well.placed component inComponents _ sits with same | ⟨marked, -, same, isMarked⟩
    · cases place with
      | bvar outer => simp [liftBVars] at same; omega
      | _ => simp [liftBVars] at same
    · simp only [Pattern.bvar.injEq] at same
      subst same
      exact isMarked

open Mettapedia.GSLT.LanguageDef.RestrictionBlocks (rename freeIn_rename copyOf outsideOf mem_outsideOf
  canonicalOf freeIn_canonicalOf permute_of_ge freeIn_toPattern)

/-- The restrictions of a block outside some of them, and those, are all of them. -/
theorem outsideOf_length_add {count : Nat} {restrictions : List Nat} (nodup : restrictions.Nodup)
    (inside : ∀ index ∈ restrictions, index < count) :
    (outsideOf count restrictions).length + restrictions.length = count := by
  have split := List.length_eq_length_filter_add (l := List.range count) (fun index => !restrictions.contains index)
  have same : ((List.range count).filter fun index => !!restrictions.contains index).length = restrictions.length := by
    simp only [Bool.not_not]
    apply List.Perm.length_eq
    apply (List.perm_ext_iff_of_nodup (List.nodup_range.filter _) nodup).mpr
    intro index
    simp only [List.mem_filter, List.mem_range, List.contains_iff_mem]
    exact ⟨fun ⟨_, member⟩ => member, fun member => ⟨inside index member, member⟩⟩
  rw [List.length_range] at split
  simp only [outsideOf] at *
  omega

/-- **A copy sits at its replicated component's place, at the block's own place**: the copy uses that place from
outside the block, so the argument, whose canonical form is the copy's, uses it too, and the argument uses from
outside only its place among the locations. -/
theorem copy_placed_outer {isLoc : Pattern → Prop} {outer count : Nat} {components : List Pattern}
    (well : WellLocated isLoc (.bvar outer) ⟨count, components⟩) {argument at' : Pattern}
    (repMember : Pattern.apply "LRep" [argument] ∈ components)
    (repPlace : placeAt (.apply "LRep" [argument]) = some at') {group : Group}
    (ownedNodup : group.restrictions.Nodup) (ownedInside : ∀ index ∈ group.restrictions, index < count)
    (allowedOnly : ∀ index ∈ group.restrictions, mentions index (.apply "LRep" [argument]) = false)
    {component : Pattern} (inGroup : component ∈ group.components)
    (sits : placeAt component = some (.bvar (outer + count)))
    (copied : canonicalOf Mettapedia.Languages.ProcessCalculi.Ambient.Located.locatedRepBlock
        (copyOf locatedBlock count group) =
      canonicalOf Mettapedia.Languages.ProcessCalculi.Ambient.Located.locatedRepBlock
        (rename (Prenex.groupIndex count (outsideOf count group.restrictions)) argument)) :
    Pattern.bvar (outer + count) = at' := by
  set owned := group.restrictions with ownedIs
  have fresh : Mettapedia.Languages.ProcessCalculi.Ambient.Located.locatedRepBlock.replicate ∉
      Mettapedia.Languages.ProcessCalculi.Ambient.Located.locatedRepBlock.emptyUnits := by decide
  have restrictFresh : Mettapedia.Languages.ProcessCalculi.Ambient.Located.locatedRepBlock.replicate ≠
      Mettapedia.Languages.ProcessCalculi.Ambient.Located.locatedRepBlock.restrict := by decide
  -- the copy uses the block's place from outside
  have uses : FreeIn (outer + count) component := freeIn_placeAt sits
  have copyUses : FreeIn (outer + count - owned.length) (copyOf locatedBlock count group) := by
    rw [copyOf]
    refine (freeIn_toPattern (block := Mettapedia.Languages.ProcessCalculi.Ambient.Located.locatedRepBlock)).mpr ?_
    refine ⟨rename _ component, List.mem_map.mpr ⟨component, inGroup, rfl⟩, ?_⟩
    rw [show outer + count - owned.length + owned.length = outer + count by
      have := outsideOf_length_add ownedNodup ownedInside; omega]
    exact (freeIn_rename component).mpr ⟨outer + count, uses, permute_of_ge _ (by omega)⟩
  have argumentRenamedUses := (freeIn_canonicalOf fresh restrictFresh _ _).mp
    (copied ▸ (freeIn_canonicalOf fresh restrictFresh _ _).mpr copyUses)
  obtain ⟨original, argumentUses, mapped⟩ := (freeIn_rename argument).mp argumentRenamedUses
  have total := outsideOf_length_add ownedNodup ownedInside
  -- the argument uses that very place
  have originalIs : original = outer + count := by
    simp only [Prenex.groupIndex] at mapped
    split_ifs at mapped with below
    · exfalso
      have notOwned : original ∉ owned := by
        intro member
        have unmentioned := allowedOnly original member
        have : mentions original (.apply "LRep" [argument]) = true :=
          (mentions_iff _ original).mpr (freeIn_apply.mpr ⟨argument, List.mem_cons_self, argumentUses⟩)
        rw [this] at unmentioned
        exact Bool.noConfusion unmentioned
      have outside : original ∈ outsideOf count owned := mem_outsideOf.mpr ⟨below, notOwned⟩
      have := List.idxOf_lt_length_iff.mpr outside
      omega
    · omega
  subst originalIs
  -- it is the argument's place
  have argumentWell := match well with
    | .intro _ _ _ _ _ _ reps _ _ _ _ _ => reps _ repMember argument at' rfl repPlace
  obtain ⟨inner, innerMember, innerFree⟩ :=
    (Mettapedia.GSLT.LanguageDef.RestrictionBlocks.freeIn_decompose (block := locatedBlock) argument _).mp
      argumentUses
  rcases argumentWell.freeIn_outer (insideLoc_locVariables isLoc count components) inner innerMember _ innerFree
      (Nat.le_add_left _ _) with same | apart
  · simpa using same
  · exfalso
    apply apart
    simp only [Nat.add_sub_cancel, insideLoc, show ¬ outer + count < count by omega, if_false,
      show outer + count - count = outer by omega]
    exact well.placeIsLoc

end Mettapedia.Languages.ProcessCalculi.Ambient.Decoding
