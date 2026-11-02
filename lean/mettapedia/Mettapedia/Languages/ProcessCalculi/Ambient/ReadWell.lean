import Mettapedia.Languages.ProcessCalculi.Ambient.ReadRoot

/-!
# The reacted block is well-located

A reaction of a well-located block leaves a well-located block: the capability gone, the rewritten marker replaced by
one with the same location and name, the continuation's components beside the rest under its restrictions
(`reacted_well`). Locations stay marked by the same markers (`marked_reactList`), each location keeps at most one
marker (`unique_reactList`), and the locations still nest: an exit or an opening keeps the depths of the block; an
entry pushes the depths of everything inside the moving ambient past the target's.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.Ambient.Steps

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Substitution (liftBVars)
open Mettapedia.GSLT.LanguageDef.WellSorted (HasType FreeTypeContext)
open Mettapedia.GSLT.LanguageDef.RestrictionBlocks (Prenex Members decompose rename rename_bvar rename_id
  liftBVars_eq_rename shiftAbove)
open Mettapedia.Languages.ProcessCalculi.Ambient.Located (locatedCalc locatedBlock)
open Mettapedia.Languages.ProcessCalculi.Ambient.Decoding (isVariable Reaches placedAt placeAt childOf markers
  capabilities placeAt_ofMarker placeAt_capability WellLocated ComponentKind Marked nameOf insideLoc Nested
  LocVariables childOf_eq_some childOf_bvar_of_kind childOf_rename shiftAbove_injective eq_of_filter_length_le_one
  messageOf inputs)

/-! ## Markers after a reaction -/

section Reacted

variable {capability marker marker' : Pattern} {components : List Pattern}

/-- **A reaction keeps every location's markers**: the rewritten marker's location is its replacement's. -/
theorem marked_reactList (capabilityNoChild : childOf capability = none)
    (movedChild : childOf marker' = childOf marker) (markerIn : marker ∈ components) (index : Nat) :
    Marked (reactList capability marker marker' components) index ↔ Marked components index := by
  constructor
  · rintro ⟨component, member, isChild⟩
    rcases mem_reactList member with inComponents | rfl
    · exact ⟨component, inComponents, isChild⟩
    · exact ⟨marker, markerIn, movedChild ▸ isChild⟩
  · rintro ⟨component, member, isChild⟩
    have notCapability : component ≠ capability := fun same => by
      rw [same, capabilityNoChild] at isChild
      cases isChild
    have inErased := (List.mem_erase_of_ne notCapability).mpr member
    by_cases isMarker : component = marker
    · subst isMarker
      exact ⟨marker', List.mem_map.mpr ⟨component, inErased, by simp⟩, by rw [movedChild]; exact isChild⟩
    · exact ⟨component, List.mem_map.mpr ⟨component, inErased, by simp [isMarker]⟩, isChild⟩

/-- **A reaction keeps at most one marker at each location.** -/
theorem unique_reactList (movedChild : childOf marker' = childOf marker)
    (unique : ∀ child, (components.filter fun component => childOf component == some child).length ≤ 1)
    (child : Pattern) :
    ((reactList capability marker marker' components).filter fun component => childOf component == some child).length
      ≤ 1 := by
  unfold reactList
  rw [List.filter_map, List.length_map]
  have same : (fun component => childOf component == some child) ∘
      (fun component => if component = marker then marker' else component) =
      fun component => childOf component == some child := by
    funext component
    simp only [Function.comp]
    split_ifs with isMarker
    · rw [movedChild, isMarker]
    · rfl
  rw [same]
  exact le_trans ((List.erase_sublist).filter _).length_le (unique child)

end Reacted

/-! ## The block before the continuation joins it -/

/-- **A reaction leaves a well-located block**, before its continuation joins it: the capability gone, the rewritten
marker replaced by a marker of the same location and name placed at a marked place. -/
theorem reacted_block_well {isLoc : Pattern → Prop} {place : Pattern} {count : Nat} {components : List Pattern}
    (well : WellLocated isLoc place ⟨count, components⟩) {capability marker marker' : Pattern}
    (capabilityNoChild : childOf capability = none) (markerIn : marker ∈ components)
    (movedChild : childOf marker' = childOf marker) (movedName : nameOf marker' = nameOf marker)
    (movedKind : ComponentKind count marker')
    (movedPlaced : ∀ at', placeAt marker' = some at' →
      at' = liftBVars 0 count place ∨ ∃ index < count, at' = .bvar index ∧ Marked components index)
    (movedNotCapability : ∀ label at' name continuation, marker' = .apply label [at', name, continuation] →
      label ∉ capabilities)
    (movedNotReplication : ∀ argument, marker' ≠ .apply "LRep" [argument])
    (movedNoMessage : messageOf marker' = none)
    (movedNotCap : ∀ at' message continuation, marker' ≠ .apply "LCap" [at', message, continuation])
    (movedNotInput : ∀ label at' binder body, marker' = .apply label [at', .lambda binder body] → label ∉ inputs)
    (nested : Nested count (reactList capability marker marker' components)) :
    WellLocated isLoc place ⟨count, reactList capability marker marker' components⟩ := by
  have markedSame := marked_reactList (components := components) capabilityNoChild movedChild markerIn
  have locSame : insideLoc isLoc count (reactList capability marker marker' components) =
      insideLoc isLoc count components := by
    funext pattern
    cases pattern with
    | bvar index =>
        simp only [insideLoc]
        split_ifs
        · exact propext (markedSame index)
        · rfl
    | _ => rfl
  have uniqueAny := well.unique_any
  cases well with
  | intro placeLoc kinds placed unique names caps reps repsPlaced _ messages capConts bodies =>
      refine .intro placeLoc (fun component member => ?_) (fun component member at' sits => ?_)
        (fun index => unique_reactList movedChild uniqueAny (.bvar index))
        (fun component member name isName => ?_) (fun component member label at' name continuation isCapability
          listed => ?_) (fun component member argument at' isReplication sits => ?_)
        (fun component member argument isReplication => ?_) nested
        (fun component member message isMsgOf => ?_)
        (fun component member at' message continuation isCapComponent => ?_)
        (fun component member label at' binder body isInput listed => ?_)
      · rcases mem_reactList member with inComponents | rfl
        · exact kinds component inComponents
        · exact movedKind
      · rcases mem_reactList member with inComponents | rfl
        · rcases placed component inComponents at' sits with atRoot | ⟨index, below, same, isMarked⟩
          · exact .inl atRoot
          · exact .inr ⟨index, below, same, (markedSame index).mpr isMarked⟩
        · rcases movedPlaced at' sits with atRoot | ⟨index, below, same, isMarked⟩
          · exact .inl atRoot
          · exact .inr ⟨index, below, same, (markedSame index).mpr isMarked⟩
      · rw [locSame]
        rcases mem_reactList member with inComponents | rfl
        · exact names component inComponents name isName
        · exact names marker markerIn name (movedName ▸ isName)
      · rw [locSame]
        rcases mem_reactList member with inComponents | rfl
        · exact caps component inComponents label at' name continuation isCapability listed
        · exact absurd listed (movedNotCapability label at' name continuation isCapability)
      · rw [locSame]
        rcases mem_reactList member with inComponents | rfl
        · exact reps component inComponents argument at' isReplication sits
        · exact absurd isReplication (movedNotReplication argument)
      · rcases mem_reactList member with inComponents | rfl
        · exact repsPlaced component inComponents argument isReplication
        · exact absurd isReplication (movedNotReplication argument)
      · rw [locSame]
        rcases mem_reactList member with inComponents | rfl
        · exact messages component inComponents message isMsgOf
        · rw [movedNoMessage] at isMsgOf
          cases isMsgOf
      · rw [locSame]
        rcases mem_reactList member with inComponents | rfl
        · exact capConts component inComponents at' message continuation isCapComponent
        · exact absurd isCapComponent (movedNotCap at' message continuation)
      · rw [locSame]
        rcases mem_reactList member with inComponents | rfl
        · exact bodies component inComponents label at' binder body isInput listed
        · exact absurd listed (movedNotInput label at' binder body isInput)

/-! ## The continuation beside the reacted block -/

open Mettapedia.GSLT.LanguageDef.RestrictionBlocks (rename_fvar)
open Mettapedia.Languages.ProcessCalculi.Ambient.Decoding (placeAt_rename)

/-- **The locations marked beside the continuation**: the reacted block's, lifted past the continuation's
restrictions, and the continuation's own. -/
theorem marked_join {count owned : Nat} {reacted group : List Pattern}
    (reactedKinds : ∀ component ∈ reacted, ComponentKind count component)
    (groupChildren : ∀ component ∈ group, ∀ child, childOf component = some child →
      ∃ index < owned, child = .bvar index) (index : Nat) :
    Marked (reacted.map (liftBVars 0 owned) ++ group) index ↔
      (owned ≤ index ∧ Marked reacted (index - owned)) ∨ (index < owned ∧ Marked group index) := by
  constructor
  · rintro ⟨component, member, isChild⟩
    rcases List.mem_append.mp member with inReacted | inGroup
    · obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp inReacted
      rw [liftBVars_eq_rename, childOf_rename] at isChild
      cases found : childOf original with
      | none => rw [found] at isChild; cases isChild
      | some child =>
          rw [found] at isChild
          obtain ⟨childIndex, below, rfl⟩ := childOf_bvar_of_kind (reactedKinds original originalMember) found
          simp only [Option.map_some, rename_bvar, shiftAbove, Nat.not_lt_zero, if_false, Option.some.injEq,
            Pattern.bvar.injEq] at isChild
          subst isChild
          exact .inl ⟨by omega, original, originalMember, by rw [found, Nat.add_sub_cancel]⟩
    · obtain ⟨childIndex, below, same⟩ := groupChildren component inGroup _ isChild
      simp only [Pattern.bvar.injEq] at same
      subst same
      exact .inr ⟨below, component, inGroup, isChild⟩
  · rintro (⟨above, component, member, isChild⟩ | ⟨below, component, member, isChild⟩)
    · refine ⟨liftBVars 0 owned component, List.mem_append_left _ (List.mem_map_of_mem member), ?_⟩
      rw [liftBVars_eq_rename, childOf_rename, isChild, Option.map_some, rename_bvar]
      simp only [shiftAbove, Nat.not_lt_zero, if_false, Option.some.injEq, Pattern.bvar.injEq]
      omega
    · exact ⟨component, List.mem_append_right _ member, isChild⟩

/-- **The reacted block beside the continuation is well-located**: the reacted block lifted past the continuation's
restrictions, the continuation's components as they are, its home a marked place or the root. -/
theorem join_well {isLoc : Pattern → Prop} {place : Pattern} {count : Nat} {components reacted : List Pattern}
    (reactedWell : WellLocated isLoc place ⟨count, reacted⟩)
    (markedSame : ∀ index, Marked reacted index ↔ Marked components index)
    {home : Pattern} {owned : Nat} {group : List Pattern}
    (groupWell : WellLocated (insideLoc isLoc count components) home ⟨owned, group⟩)
    (homePlaced : home = liftBVars 0 count place ∨ ∃ index < count, home = .bvar index ∧ Marked components index) :
    WellLocated isLoc place ⟨count + owned, reacted.map (liftBVars 0 owned) ++ group⟩ := by
  have reactedKinds := reactedWell.kinds
  have groupKinds := groupWell.kinds
  simp only at reactedKinds groupKinds
  have groupChildren : ∀ component ∈ group, ∀ child, childOf component = some child →
      ∃ index < owned, child = .bvar index := fun component member _ isChild =>
    childOf_bvar_of_kind (groupKinds component member) isChild
  have marked := marked_join (owned := owned) reactedKinds groupChildren
  have liftIs : ∀ cutoff shift, liftBVars cutoff shift = rename (shiftAbove cutoff shift) :=
    fun cutoff shift => funext fun pattern => liftBVars_eq_rename cutoff shift pattern
  have firstHalf := WellLocated.embed (total := count + owned) (bigger := reacted.map (liftBVars 0 owned) ++ group)
    reactedWell (shiftAbove_injective 0 owned)
    (.inl (by
      rw [← liftIs, Mettapedia.GSLT.LanguageDef.RestrictionBlocks.liftBVars_liftBVars, Nat.add_comm]))
    (fun index below => by simp [shiftAbove]; omega)
    (fun index below => by
      simp only [shiftAbove, Nat.not_lt_zero, if_false, marked]
      constructor
      · rintro (⟨-, isMarked⟩ | ⟨tooSmall, -⟩)
        · simpa using isMarked
        · omega
      · intro isMarked
        exact .inl ⟨by omega, by simpa using isMarked⟩)
    (fun pattern isVar => by
      cases pattern with
      | bvar index =>
          simp only [rename_bvar, shiftAbove, Nat.not_lt_zero, if_false, insideLoc]
          by_cases below : index < count
          · simp only [show index + owned < count + owned by omega, below, if_true, marked]
            constructor
            · rintro (⟨-, isMarked⟩ | ⟨tooSmall, -⟩)
              · simpa using isMarked
              · omega
            · intro isMarked
              exact .inl ⟨by omega, by simpa using isMarked⟩
          · simp only [show ¬ index + owned < count + owned by omega, below, if_false]
            rw [show index + owned - (count + owned) = index - count by omega]
      | fvar name => simp [rename_fvar, insideLoc]
      | _ => simp [isVariable] at isVar)
  have secondHalf := WellLocated.embed (total := count + owned) (bigger := reacted.map (liftBVars 0 owned) ++ group)
    (relabel := id) (placeBig := place) groupWell (fun _ _ same => same)
    (by
      rw [rename_id]
      rcases homePlaced with atRoot | ⟨index, below, rfl, isMarked⟩
      · left
        rw [atRoot, Mettapedia.GSLT.LanguageDef.RestrictionBlocks.liftBVars_liftBVars, Nat.add_comm]
      · right
        refine ⟨index + owned, by omega, by simp [liftBVars], (marked _).mpr (.inl ⟨by omega, ?_⟩)⟩
        rw [Nat.add_sub_cancel]
        exact (markedSame index).mpr isMarked)
    (fun index below => by simp only [id]; omega)
    (fun index below => by
      simp only [id, marked]
      constructor
      · rintro (⟨tooBig, -⟩ | ⟨-, isMarked⟩)
        · omega
        · exact isMarked
      · intro isMarked
        exact .inr ⟨below, isMarked⟩)
    (fun pattern isVar => by
      rw [rename_id]
      cases pattern with
      | bvar index =>
          simp only [insideLoc]
          by_cases low : index < owned
          · simp only [low, if_true, show index < count + owned by omega]
            rw [marked]
            constructor
            · rintro (⟨tooBig, -⟩ | ⟨-, isMarked⟩)
              · omega
              · exact isMarked
            · intro isMarked
              exact .inr ⟨low, isMarked⟩
          · by_cases middle : index < count + owned
            · simp only [low, if_false, middle, if_true, show index - owned < count by omega]
              rw [marked]
              constructor
              · rintro (⟨-, isMarked⟩ | ⟨tooSmall, -⟩)
                · exact (markedSame _).mp isMarked
                · exact absurd tooSmall low
              · intro isMarked
                exact .inl ⟨by omega, (markedSame _).mpr isMarked⟩
            · simp only [low, if_false, middle, show ¬ index - owned < count by omega]
              rw [show index - (count + owned) = index - owned - count by omega]
      | fvar name => simp [insideLoc]
      | _ => simp [isVariable] at isVar)
  simp only [← liftIs] at firstHalf
  have both : ∀ component ∈ reacted.map (liftBVars 0 owned) ++ group, _ := fun component member =>
    (List.mem_append.mp member).elim (firstHalf component) fun inGroup =>
      secondHalf component (List.mem_map.mpr ⟨component, inGroup, rename_id component⟩)
  refine .intro reactedWell.placeIsLoc (fun component member => (both component member).1)
    (fun component member => (both component member).2.1) ?_ (fun component member => (both component member).2.2.1)
    (fun component member => (both component member).2.2.2.1)
    (fun component member => (both component member).2.2.2.2.1)
    (fun component member => (both component member).2.2.2.2.2.1) ?_
    (fun component member => (both component member).2.2.2.2.2.2.1)
    (fun component member => (both component member).2.2.2.2.2.2.2.1)
    (fun component member => (both component member).2.2.2.2.2.2.2.2)
  · -- at most one marker at each location
    intro index
    have reactedUnique := reactedWell.unique
    have groupUnique := groupWell.unique
    simp only at reactedUnique groupUnique
    rw [List.filter_append, List.length_append]
    have firstPart : (reacted.map (liftBVars 0 owned)).filter
        (fun component => childOf component == some (.bvar index)) =
        if owned ≤ index then (reacted.filter fun component => childOf component == some (.bvar (index - owned))).map
          (liftBVars 0 owned) else [] := by
      rw [List.filter_map]
      split_ifs with above
      · congr 1
        apply List.filter_congr
        intro component member
        simp only [Function.comp, liftIs, childOf_rename]
        cases found : childOf component with
        | none => simp
        | some child =>
            obtain ⟨childIndex, below, rfl⟩ := childOf_bvar_of_kind (reactedKinds component member) found
            rw [Bool.eq_iff_iff]
            simp only [Option.map_some, rename_bvar, shiftAbove, Nat.not_lt_zero, if_false, beq_iff_eq,
              Option.some.injEq, Pattern.bvar.injEq]
            constructor <;> intro same <;> omega
      · rw [List.filter_eq_nil_iff.mpr]
        · rfl
        intro original originalMember isChild
        simp only [Function.comp, liftIs, childOf_rename, beq_iff_eq] at isChild
        cases found : childOf original with
        | none => rw [found] at isChild; cases isChild
        | some child =>
            rw [found] at isChild
            obtain ⟨childIndex, below, rfl⟩ := childOf_bvar_of_kind (reactedKinds original originalMember) found
            simp [rename_bvar, shiftAbove] at isChild
            omega
    have secondPart : group.filter (fun component => childOf component == some (.bvar index)) =
        if index < owned then group.filter (fun component => childOf component == some (.bvar index)) else [] := by
      split_ifs with low
      · rfl
      · refine List.filter_eq_nil_iff.mpr fun component member isChild => ?_
        simp only [beq_iff_eq] at isChild
        obtain ⟨childIndex, below, same⟩ := groupChildren component member _ isChild
        simp only [Pattern.bvar.injEq] at same
        omega
    rw [firstPart, secondPart]
    split_ifs with above low low
    · omega
    · simpa using reactedUnique (index - owned)
    · simpa using groupUnique index
    · simp
  · -- the locations nest: the continuation's locations past every location of the reacted block
    have nestedR : Nested count reacted := reactedWell.nested
    have nestedG : Nested owned group := groupWell.nested
    obtain ⟨depthR, growsR⟩ := nestedR
    obtain ⟨depthG, growsG⟩ := nestedG
    set big := ((List.range count).map depthR).foldr max 0 + 1 with bigIs
    have belowBig : ∀ index < count, depthR index < big := fun index below => by
      have := Mettapedia.GSLT.LanguageDef.RestrictionBlocks.le_foldr_max
        (List.mem_map_of_mem (f := depthR) (List.mem_range.mpr below))
      omega
    refine ⟨fun index => if index < owned then big + depthG index else depthR (index - owned), ?_⟩
    intro component member index child below childBelow sits isChild
    rcases List.mem_append.mp member with inReacted | inGroup
    · obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp inReacted
      rw [liftIs, placeAt_rename] at sits
      rw [liftIs, childOf_rename] at isChild
      cases foundChild : childOf original with
      | none => rw [foundChild] at isChild; cases isChild
      | some originalChild =>
          rw [foundChild] at isChild
          obtain ⟨childIndex, childLow, rfl⟩ := childOf_bvar_of_kind (reactedKinds original originalMember) foundChild
          simp only [Option.map_some, rename_bvar, shiftAbove, Nat.not_lt_zero, if_false, Option.some.injEq,
            Pattern.bvar.injEq] at isChild
          cases foundPlace : placeAt original with
          | none => rw [foundPlace] at sits; cases sits
          | some originalPlace =>
              rw [foundPlace, Option.map_some, Option.some.injEq] at sits
              cases originalPlace with
              | bvar placeIndex =>
                  simp only [rename_bvar, shiftAbove, Nat.not_lt_zero, if_false, Pattern.bvar.injEq] at sits
                  subst sits isChild
                  simp only [show ¬ placeIndex + owned < owned by omega, show ¬ childIndex + owned < owned by omega,
                    if_false, Nat.add_sub_cancel]
                  exact growsR original originalMember placeIndex childIndex (by omega) childLow foundPlace foundChild
              | fvar name => simp [Mettapedia.GSLT.LanguageDef.RestrictionBlocks.rename_fvar] at sits
              | apply label arguments =>
                  simp [Mettapedia.GSLT.LanguageDef.RestrictionBlocks.rename_apply] at sits
              | lambda binder body =>
                  simp [Mettapedia.GSLT.LanguageDef.RestrictionBlocks.rename_lambda] at sits
              | multiLambda arity binders body =>
                  simp [Mettapedia.GSLT.LanguageDef.RestrictionBlocks.rename_multiLambda] at sits
              | subst body replacement =>
                  simp [Mettapedia.GSLT.LanguageDef.RestrictionBlocks.rename_subst] at sits
              | collection kind elements rest =>
                  simp [Mettapedia.GSLT.LanguageDef.RestrictionBlocks.rename_collection] at sits
    · obtain ⟨childIndex, childLow, same⟩ := groupChildren component inGroup _ isChild
      simp only [Pattern.bvar.injEq] at same
      have childLow' : child < owned := same ▸ childLow
      by_cases placeLow : index < owned
      · simp only [placeLow, childLow', if_true]
        have := growsG component inGroup index child placeLow childLow' sits isChild
        omega
      · simp only [placeLow, childLow', if_true, if_false]
        have := belowBig (index - owned) (by omega)
        omega

/-! ## Each kind of reaction keeps the block well-located -/

/-- **An entry keeps the locations nested**: everything inside the moving ambient gets deeper than the target. -/
theorem nested_enter {count : Nat} {components : List Pattern} {depth : Nat → Nat}
    (children : ∀ component ∈ components, ∀ child, childOf component = some child →
      ∃ index < count, child = .bvar index)
    (grows : ∀ component ∈ components, ∀ index child, index < count → child < count →
      placeAt component = some (.bvar index) → childOf component = some (.bvar child) → depth index < depth child)
    (unique : ∀ child, (components.filter fun component => childOf component == some child).length ≤ 1)
    {capability parent : Pattern} {mover target : Nat} {moverName targetName : Pattern}
    (markerIn : Pattern.apply "LAmb" [parent, .bvar mover, moverName] ∈ components)
    (destinationIn : Pattern.apply "LAmb" [parent, .bvar target, targetName] ∈ components)
    (moverBelow : mover < count) (apartTargets : mover ≠ target) :
    Nested count (reactList capability (.apply "LAmb" [parent, .bvar mover, moverName])
      (.apply "LAmb" [.bvar target, .bvar mover, moverName]) components) := by
  classical
  set marker := Pattern.apply "LAmb" [parent, .bvar mover, moverName] with markerIs
  set marker' := Pattern.apply "LAmb" [.bvar target, .bvar mover, moverName] with marker'Is
  set destination := Pattern.apply "LAmb" [parent, .bvar target, targetName] with destinationIs
  have ambMarker : "LAmb" ∈ markers := by simp [markers]
  have within : ∀ component ∈ components, component ∈ components := fun _ member => member
  have onlyChild : ∀ first ∈ components, ∀ second ∈ components, ∀ child, childOf first = some child →
      childOf second = some child → first = second := fun first firstIn second secondIn child firstChild secondChild =>
    eq_of_filter_length_le_one (unique child) firstIn secondIn (by simp [firstChild]) (by simp [secondChild])
  have markerChild : childOf marker = some (.bvar mover) := by simp [markerIs, childOf, markers]
  have destinationChild : childOf destination = some (.bvar target) := by simp [destinationIs, childOf, markers]
  have markerAt : placeAt marker = some parent := placeAt_ofMarker ambMarker _ _ _
  have destinationAt : placeAt destination = some parent := placeAt_ofMarker ambMarker _ _ _
  -- the target is not inside the moving ambient
  have targetOutside : ¬ Reaches components (.bvar mover) (.bvar target) := by
    intro inside
    obtain ⟨last, lastIn, lastChild, at', lastPlaced, reachedLast⟩ :=
      Reaches.penultimate inside (by simpa using apartTargets)
    rw [onlyChild last lastIn destination destinationIn _ lastChild destinationChild, destinationAt] at lastPlaced
    obtain rfl := Option.some.inj lastPlaced
    have back := reaches_antisymm children grows within within reachedLast
      (.down markerIn (by simp [placedAt, markerAt]) markerChild .here)
    exact child_ne_place children grows markerIn (by simp [placedAt, markerAt]) markerChild back
  have markerOut : marker ∉ reactList capability marker marker' components := by
    intro inReacted
    obtain ⟨original, inErased, same⟩ := List.mem_map.mp inReacted
    split_ifs at same with isMarker
    · simp [marker'Is, markerIs] at same
      exact child_ne_place children grows destinationIn (by simp [placedAt, destinationAt]) destinationChild same
    · exact isMarker same
  set shift := depth target + 1 with shiftIs
  refine ⟨fun index => depth index + if Reaches components (.bvar mover) (.bvar index) then shift else 0, ?_⟩
  intro component member index child below childBelow sits isChild
  rcases mem_reactList member with inComponents | rfl
  · have different : component ≠ marker := fun same => markerOut (same ▸ member)
    have step := grows component inComponents index child below childBelow sits isChild
    by_cases placeInside : Reaches components (.bvar mover) (.bvar index)
    · have childInside := Reaches.extend placeInside inComponents sits isChild
      simp only [placeInside, childInside, if_true]
      omega
    · by_cases childInside : Reaches components (.bvar mover) (.bvar child)
      · exfalso
        by_cases isMover : child = mover
        · subst isMover
          exact different (onlyChild component inComponents marker markerIn _ isChild markerChild)
        · obtain ⟨last, lastIn, lastChild, at', lastPlaced, reachedLast⟩ :=
            Reaches.penultimate childInside (by simpa using Ne.symm isMover)
          rw [onlyChild last lastIn component inComponents _ lastChild isChild, sits] at lastPlaced
          obtain rfl := Option.some.inj lastPlaced
          exact placeInside reachedLast
      · simp only [placeInside, childInside, if_false]
        omega
  · have placeIs : placeAt marker' = some (.bvar target) := placeAt_ofMarker ambMarker _ _ _
    rw [placeIs, Option.some.injEq, Pattern.bvar.injEq] at sits
    have childIs : childOf marker' = some (.bvar mover) := by simp [marker'Is, childOf, markers]
    rw [childIs, Option.some.injEq, Pattern.bvar.injEq] at isChild
    subst sits isChild
    simp only [targetOutside, if_false, Reaches.here, if_true]
    omega

open Mettapedia.Languages.ProcessCalculi.Ambient.Decoding (not_capability_of_marker not_marker_of_capability)

/-- **A reaction of a well-located block leaves a well-located block**: the reacted components lifted past the
continuation's restrictions, beside the continuation's components. -/
theorem reacted_well {isLoc : Pattern → Prop} {place : Pattern} {count : Nat} {components : List Pattern}
    (well : WellLocated isLoc place ⟨count, components⟩)
    {redex : LocRedex} {rest : List Pattern} (split : components.Perm (redex.parts ++ rest))
    {owned : Nat} {group : List Pattern} (decomposed : decompose locatedBlock redex.continuationOf = ⟨owned, group⟩) :
    WellLocated isLoc place ⟨count + owned,
      (reactList redex.capabilityPart redex.markerPart redex.movedPart components).map (liftBVars 0 owned) ++
        group⟩ := by
  have partsIn : ∀ part ∈ redex.capabilityPart :: redex.markerPart :: redex.keptParts, part ∈ components :=
    fun part member => split.symm.subset (List.mem_append_left _ ((LocRedex.parts_perm redex).symm.subset member))
  have capabilityIn := partsIn _ List.mem_cons_self
  have markerIn := partsIn _ (List.mem_cons_of_mem _ List.mem_cons_self)
  have keptIn : ∀ part ∈ redex.keptParts, part ∈ components := fun part member =>
    partsIn part (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ member))
  have twoParts : components.Perm (redex.markerPart :: redex.capabilityPart :: (redex.keptParts ++ rest)) :=
    split.trans (((LocRedex.parts_perm redex).append_right rest).trans (.swap _ _ _))
  have kinds : ∀ component ∈ components, ComponentKind count component := well.kinds
  have placed : ∀ component ∈ components, ∀ at', placeAt component = some at' →
      at' = liftBVars 0 count place ∨ ∃ index < count, at' = .bvar index ∧ Marked components index := well.placed
  have nested : Nested count components := well.nested
  obtain ⟨depth, grows⟩ := nested
  have children : ∀ component ∈ components, ∀ child, childOf component = some child →
      ∃ index < count, child = .bvar index := fun component member _ isChild =>
    childOf_bvar_of_kind (kinds component member) isChild
  have unique := well.unique_any
  have ambMarker : "LAmb" ∈ markers := by simp [markers]
  -- the reaction leaves a well-located block, then the continuation joins it
  have finish : ∀ {label : String} {home name : Pattern}, label ∈ capabilities →
      redex.capabilityPart = .apply label [home, name, redex.continuationOf] →
      WellLocated isLoc place ⟨count, reactList redex.capabilityPart redex.markerPart redex.movedPart components⟩ →
      childOf redex.movedPart = childOf redex.markerPart →
      WellLocated isLoc place ⟨count + owned,
        (reactList redex.capabilityPart redex.markerPart redex.movedPart components).map (liftBVars 0 owned) ++
          group⟩ := by
    intro label home name listed shape reactedWell movedChild
    have capabilityNoChild : childOf redex.capabilityPart = none := by
      rw [shape]
      simp [childOf, not_marker_of_capability listed]
    have markedSame := marked_reactList (components := components) capabilityNoChild movedChild markerIn
    rw [shape] at capabilityIn
    have groupWell := WellLocated.continuation well capabilityIn listed
    rw [decomposed] at groupWell
    exact join_well reactedWell markedSame groupWell (placed _ capabilityIn home (placeAt_capability listed _ _ _))
  cases redex with
  | «open» at' location name continuation =>
      simp only [LocRedex.capabilityPart, LocRedex.markerPart, LocRedex.movedPart, LocRedex.continuationOf]
        at markerIn capabilityIn finish decomposed ⊢
      have openListed : "LOpen" ∈ capabilities := by simp [capabilities]
      have openedMarker : "LOpened" ∈ markers := by simp [markers]
      obtain ⟨locationIndex, locationBelow, rfl⟩ := children _ markerIn location (by simp [childOf, markers])
      refine finish openListed rfl ?_ (by simp [childOf, markers])
      refine reacted_block_well well (by simp [childOf, not_marker_of_capability openListed]) markerIn
        (by simp [childOf, markers]) (by simp [nameOf, markers]) (.marker openedMarker locationBelow)
        (fun at'' sits => placed _ markerIn at'' (by
          rw [placeAt_ofMarker openedMarker] at sits
          rw [placeAt_ofMarker ambMarker]
          exact sits))
        (fun label at'' name' continuation' same listed => by
          simp only [Pattern.apply.injEq] at same
          rw [← same.1] at listed
          simp [capabilities] at listed)
        (fun argument same => by simp at same) (by simp [messageOf]) (fun _ _ _ same => by simp at same)
        (fun _ _ _ _ same => by simp at same)
        ⟨depth, fun component member index child below childBelow sits isChild => ?_⟩
      rcases mem_reactList member with inComponents | rfl
      · exact grows component inComponents index child below childBelow sits isChild
      · rw [placeAt_ofMarker openedMarker] at sits
        exact grows _ markerIn index child below childBelow (by rw [placeAt_ofMarker ambMarker]; exact sits)
          (by simpa [childOf, markers] using isChild)
  | move entering parent mover target moverName targetName continuation =>
      cases entering with
      | true =>
          simp only [LocRedex.capabilityPart, LocRedex.markerPart, LocRedex.movedPart, LocRedex.continuationOf,
            LocRedex.keptParts, LocRedex.capability, LocRedex.before, LocRedex.after, if_true]
            at markerIn capabilityIn keptIn twoParts finish decomposed ⊢
          have inListed : "LIn" ∈ capabilities := by simp [capabilities]
          have destinationIn := keptIn _ List.mem_cons_self
          obtain ⟨moverIndex, moverBelow, rfl⟩ := children _ markerIn mover (by simp [childOf, markers])
          obtain ⟨targetIndex, targetBelow, rfl⟩ := children _ destinationIn target (by simp [childOf, markers])
          have apartTargets : moverIndex ≠ targetIndex := by
            intro same
            subst same
            exact two_kept_absurd (keep := fun component => childOf component == some (.bvar moverIndex))
              (unique _) (twoParts.trans (.cons _ (.swap _ _ _))) (by simp [childOf, markers])
              (by simp [childOf, markers])
          refine finish inListed rfl ?_ (by simp [childOf, markers])
          refine reacted_block_well well (by simp [childOf, not_marker_of_capability inListed]) markerIn
            (by simp [childOf, markers]) (by simp [nameOf, markers]) (.marker ambMarker moverBelow)
            (fun at'' sits => by
              rw [placeAt_ofMarker ambMarker] at sits
              obtain rfl := Option.some.inj sits
              exact .inr ⟨targetIndex, targetBelow, rfl, _, destinationIn, by simp [childOf, markers]⟩)
            (fun label at'' name' continuation' same listed => by
              simp only [Pattern.apply.injEq] at same
              rw [← same.1] at listed
              simp [capabilities] at listed)
            (fun argument same => by simp at same) (by simp [messageOf]) (fun _ _ _ same => by simp at same)
            (fun _ _ _ _ same => by simp at same)
            (nested_enter children grows unique markerIn destinationIn moverBelow apartTargets)
      | false =>
          simp only [LocRedex.capabilityPart, LocRedex.markerPart, LocRedex.movedPart, LocRedex.continuationOf,
            LocRedex.keptParts, LocRedex.capability, LocRedex.before, LocRedex.after, Bool.false_eq_true, if_false]
            at markerIn capabilityIn keptIn twoParts finish decomposed ⊢
          have outListed : "LOut" ∈ capabilities := by simp [capabilities]
          have destinationIn := keptIn _ List.mem_cons_self
          obtain ⟨moverIndex, moverBelow, rfl⟩ := children _ markerIn mover (by simp [childOf, markers])
          obtain ⟨targetIndex, targetBelow, rfl⟩ := children _ destinationIn target (by simp [childOf, markers])
          refine finish outListed rfl ?_ (by simp [childOf, markers])
          refine reacted_block_well well (by simp [childOf, not_marker_of_capability outListed]) markerIn
            (by simp [childOf, markers]) (by simp [nameOf, markers]) (.marker ambMarker moverBelow)
            (fun at'' sits => placed _ destinationIn at'' (by
              rw [placeAt_ofMarker ambMarker] at sits ⊢
              exact sits))
            (fun label at'' name' continuation' same listed => by
              simp only [Pattern.apply.injEq] at same
              rw [← same.1] at listed
              simp [capabilities] at listed)
            (fun argument same => by simp at same) (by simp [messageOf]) (fun _ _ _ same => by simp at same)
            (fun _ _ _ _ same => by simp at same)
            ⟨depth, fun component member index child below childBelow sits isChild => ?_⟩
          rcases mem_reactList member with inComponents | rfl
          · exact grows component inComponents index child below childBelow sits isChild
          · rw [placeAt_ofMarker ambMarker, Option.some.injEq] at sits
            subst sits
            have childIs : moverIndex = child := by simpa [childOf, markers] using isChild
            subst childIs
            have first := grows _ destinationIn index targetIndex below targetBelow
              (placeAt_ofMarker ambMarker _ _ _) (by simp [childOf, markers])
            have second := grows _ markerIn targetIndex moverIndex targetBelow moverBelow
              (placeAt_ofMarker ambMarker _ _ _) (by simp [childOf, markers])
            omega

end Mettapedia.Languages.ProcessCalculi.Ambient.Steps
