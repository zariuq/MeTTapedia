import Mettapedia.Languages.ProcessCalculi.Ambient.DecodingReach

/-!
# Reading back an absorbed copy

A copy of a replicated component's argument, sitting at the replicated component's place with its own restrictions,
reads back as the argument's reading beside the replication, which absorbs it. Restrictions only the copy uses move
down the path from the block's place to the copy's place: past the bags by extrusion, past the ambients by the
boundary law.

This file gathers the ambient equivalences the argument takes:

- restrictions used by one member of a bag move onto it (`restricts_body_extract`);
- a copy beside its replication is absorbed (`absorb_body`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.Ambient.Decoding

open Mettapedia.Languages.ProcessCalculi.Ambient.Comm (ambientCoreCalc)

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Substitution (liftBVars)
open Mettapedia.GSLT.LanguageDef.WellSorted (HasType FreeTypeContext)
open Mettapedia.GSLT.LanguageDef.RestrictionBlocks (Prenex Members ProcEquiv bag_body_equivalent extrusions_equivalent
  restricts_congr unfold_absorb_equivalent restricts_typed body_typed)
open Mettapedia.Languages.ProcessCalculi.Ambient.Full (ambientBlock ambientRepBlock)
open Mettapedia.Languages.ProcessCalculi.Ambient.Encoding (nameType procType)

variable {free : FreeTypeContext}

/-- **Restrictions one member of a bag uses move onto it**: `(νx̄){P | Q̄↑} ≡ {(νx̄)P | Q̄}`. -/
theorem restricts_body_extract {bound : List TypeExpr} (count : Nat) {inner : Pattern} {others : List Pattern}
    (innerTyped : HasType ambientCoreCalc free (List.replicate count nameType ++ bound) inner procType)
    (othersMembers : Members ambientCoreCalc ambientBlock free bound others) :
    ProcEquiv ambientCoreCalc ambientBlock free bound
      (Prenex.restricts ambientBlock count (Prenex.body ambientBlock (inner :: others.map (liftBVars 0 count))))
      (Prenex.body ambientBlock (Prenex.restricts ambientBlock count inner :: others)) := by
  have liftedMembers : Members ambientCoreCalc ambientBlock free (List.replicate count nameType ++ bound)
      (inner :: others.map (liftBVars 0 count)) := by
    intro element member
    rcases List.mem_cons.mp member with rfl | inLifted
    · exact innerTyped
    · have lifted := Members.lift (language := ambientCoreCalc) (block := ambientBlock)
        (List.replicate count nameType) othersMembers
      rw [List.length_replicate] at lifted
      exact lifted element inLifted
  have outerMembers : Members ambientCoreCalc ambientBlock free bound
      (Prenex.restricts ambientBlock count inner :: others) := by
    intro element member
    rcases List.mem_cons.mp member with rfl | inOthers
    · exact restricts_typed (language := ambientCoreCalc) (block := ambientBlock) count innerTyped
    · exact othersMembers element inOthers
  refine .trans _ _ _ (restricts_congr (language := ambientCoreCalc) (block := ambientBlock) count
    (Relation.EqvGen.symm _ _ (bag_body_equivalent liftedMembers))) ?_
  refine .trans _ _ _ (Relation.EqvGen.symm _ _
    (extrusions_equivalent (language := ambientCoreCalc) (block := ambientBlock) count innerTyped othersMembers)) ?_
  exact bag_body_equivalent outerMembers

/-- **A copy beside its replication is absorbed**, in a body. -/
theorem absorb_body {bound : List TypeExpr} {copy : Pattern} {rest : List Pattern}
    (copyTyped : HasType ambientCoreCalc free bound copy procType)
    (restMembers : Members ambientCoreCalc ambientBlock free bound rest)
    (replicated : Pattern.apply "ARep" [copy] ∈ rest) :
    ProcEquiv ambientCoreCalc ambientBlock free bound (Prenex.body ambientBlock (copy :: rest))
      (Prenex.body ambientBlock rest) := by
  have allMembers : Members ambientCoreCalc ambientBlock free bound (copy :: rest) := by
    intro element member
    rcases List.mem_cons.mp member with rfl | inRest
    · exact copyTyped
    · exact restMembers element inRest
  refine .trans _ _ _ (Relation.EqvGen.symm _ _ (bag_body_equivalent allMembers)) ?_
  refine .trans _ _ _ (unfold_absorb_equivalent (language := ambientCoreCalc) (block := ambientRepBlock) copyTyped
    restMembers replicated) ?_
  exact bag_body_equivalent restMembers

/-! ## Reaching through lifted components -/

open Mettapedia.GSLT.LanguageDef.RestrictionBlocks (rename liftBVars_eq_rename shiftAbove rename_bvar)

theorem liftBVars_injective (count : Nat) : Function.Injective (liftBVars 0 count) := by
  intro first second same
  rw [liftBVars_eq_rename, liftBVars_eq_rename] at same
  exact Mettapedia.GSLT.LanguageDef.RestrictionBlocks.rename_injective (shiftAbove_injective 0 count) same

theorem placedAt_lift (count : Nat) (place component : Pattern) :
    placedAt (liftBVars 0 count place) (liftBVars 0 count component) = placedAt place component := by
  rw [liftBVars_eq_rename, liftBVars_eq_rename]
  exact placedAt_rename (shiftAbove_injective 0 count) place component

theorem childOf_lift (count : Nat) (component : Pattern) :
    childOf (liftBVars 0 count component) = (childOf component).map (liftBVars 0 count) := by
  rw [liftBVars_eq_rename, childOf_rename]
  congr 1
  funext pattern
  rw [liftBVars_eq_rename]

/-- A lifted place is none of the lifting's own variables. -/
theorem lift_ne_owned {count : Nat} {place : Pattern} {index : Nat} (below : index < count) :
    liftBVars 0 count place ≠ .bvar index := by
  cases place with
  | bvar outer => simp [liftBVars]; omega
  | _ => simp [liftBVars]

/-- **Reading from a lifted place through lifted components and a group sitting at a lifted home or at the lifting's
own variables**: what it reaches is lifted from what the components reach, unless it reaches the home first. -/
theorem reaches_lifted {owned : Nat} {home : Pattern} :
    ∀ {others group : List Pattern} {place target : Pattern},
      (∀ component ∈ group, ∀ at', placeAt component = some at' →
        at' = liftBVars 0 owned home ∨ ∃ index < owned, at' = .bvar index) →
      Reaches (others.map (liftBVars 0 owned) ++ group) (liftBVars 0 owned place) target →
      (∃ original, target = liftBVars 0 owned original ∧ Reaches others place original) ∨ Reaches others place home := by
  intro others group place target groupPlaced reached
  generalize listIs : others.map (liftBVars 0 owned) ++ group = list at reached
  generalize placeIs : liftBVars 0 owned place = lifted at reached
  induction reached generalizing others group place with
  | here =>
      subst placeIs
      exact .inl ⟨place, rfl, .here⟩
  | @down components liftedPlace child target marker member isPlaced isChild below recurse =>
      subst listIs placeIs
      rcases List.mem_append.mp member with inOthers | inGroup
      · obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp inOthers
        rw [placedAt_lift] at isPlaced
        rw [childOf_lift] at isChild
        cases found : childOf original with
        | none => rw [found] at isChild; cases isChild
        | some originalChild =>
            rw [found, Option.map_some, Option.some.injEq] at isChild
            subst isChild
            have filtered : (others.map (liftBVars 0 owned) ++ group).filter
                (fun other => !placedAt (liftBVars 0 owned place) other) =
                (others.filter fun other => !placedAt place other).map (liftBVars 0 owned) ++
                  group.filter (fun other => !placedAt (liftBVars 0 owned place) other) := by
              rw [List.filter_append, List.filter_map]
              congr 2
              refine List.filter_congr fun other _ => ?_
              simp [placedAt_lift]
            rcases recurse (fun component inFiltered => groupPlaced component (List.mem_filter.mp inFiltered).1)
                filtered.symm rfl with ⟨deep, rfl, deeper⟩ | reachedHome
            · exact .inl ⟨deep, rfl, .down originalMember isPlaced found deeper⟩
            · exact .inr (.down originalMember isPlaced found reachedHome)
      · have sits : placeAt marker = some (liftBVars 0 owned place) := by simpa [placedAt] using isPlaced
        rcases groupPlaced marker inGroup _ sits with atHome | ⟨index, below, same⟩
        · exact .inr (by rw [liftBVars_injective owned atHome]; exact .here)
        · exact absurd same (lift_ne_owned below)

/-! ## Lists of related members -/

theorem forall₂_self {α : Type} {relation : α → α → Prop} (reflexive : ∀ element, relation element element) :
    ∀ list : List α, List.Forall₂ relation list list
  | [] => .nil
  | head :: rest => .cons (reflexive head) (forall₂_self reflexive rest)

theorem forall₂_middle {α : Type} {relation : α → α → Prop} (reflexive : ∀ element, relation element element)
    {first second : α} (related : relation first second) :
    ∀ before after : List α, List.Forall₂ relation (before ++ first :: after) (before ++ second :: after)
  | [], after => .cons related (forall₂_self reflexive after)
  | head :: before, after => .cons (reflexive head) (forall₂_middle reflexive related before after)

/-- Two members a filter keeping at most one keeps are one. -/
theorem eq_of_filter_length_le_one {keep : Pattern → Bool} {list : List Pattern}
    (atMostOne : (list.filter keep).length ≤ 1) {first second : Pattern} (firstIn : first ∈ list)
    (secondIn : second ∈ list) (firstKept : keep first = true) (secondKept : keep second = true) : first = second := by
  have firstFiltered : first ∈ list.filter keep := List.mem_filter.mpr ⟨firstIn, firstKept⟩
  have secondFiltered : second ∈ list.filter keep := List.mem_filter.mpr ⟨secondIn, secondKept⟩
  generalize list.filter keep = filtered at firstFiltered secondFiltered atMostOne
  match filtered, firstFiltered, secondFiltered, atMostOne with
  | [], firstFiltered, _, _ => simp at firstFiltered
  | [_], firstFiltered, secondFiltered, _ =>
      rw [List.mem_singleton] at firstFiltered secondFiltered
      rw [firstFiltered, secondFiltered]
  | _ :: _ :: _, _, _, atMostOne => simp at atMostOne

/-- Beside the one member of a sublist a filter keeping at most one keeps, the filter keeps nothing. -/
theorem unkept_beside {keep : Pattern → Bool} {list before after : List Pattern} {middle : Pattern}
    (sub : (before ++ middle :: after).Sublist list) (atMostOne : (list.filter keep).length ≤ 1)
    (kept : keep middle = true) : ∀ other ∈ before ++ after, keep other = false := by
  intro other member
  cases otherKept : keep other with
  | false => rfl
  | true =>
      have long := (sub.filter keep).length_le
      rw [List.filter_append, List.filter_cons_of_pos kept, List.length_append, List.length_cons] at long
      rcases List.mem_append.mp member with inBefore | inAfter
      · have positive := List.length_pos_of_mem (List.mem_filter.mpr ⟨inBefore, otherKept⟩)
        omega
      · have positive := List.length_pos_of_mem (List.mem_filter.mpr ⟨inAfter, otherKept⟩)
        omega

/-! ## Restrictions moved onto part of a body -/

open Mettapedia.GSLT.LanguageDef.RestrictionBlocks (rename_body body_pair_equivalent body_perm_equivalent body_congr
  decompose decompose_sound BlockSignature lift_typed)
open Mettapedia.Languages.ProcessCalculi.Ambient.Full (amb_typed amb_fill)
open Mettapedia.Languages.ProcessCalculi.Ambient.Located (locatedCalc locatedBlock locatedLanguage)

/-- **Restrictions only part of a body uses move onto that part**: `(νx̄){Q̄↑ | B̄} ≡ {(νx̄){B̄} | Q̄}`. -/
theorem restricts_body_split {bound : List TypeExpr} (count : Nat) {kept moved : List Pattern}
    (keptMembers : Members ambientCoreCalc ambientBlock free bound kept)
    (movedMembers : Members ambientCoreCalc ambientBlock free (List.replicate count nameType ++ bound) moved) :
    ProcEquiv ambientCoreCalc ambientBlock free bound
      (Prenex.restricts ambientBlock count (Prenex.body ambientBlock (kept.map (liftBVars 0 count) ++ moved)))
      (Prenex.body ambientBlock (Prenex.restricts ambientBlock count (Prenex.body ambientBlock moved) :: kept)) := by
  have liftedMembers : Members ambientCoreCalc ambientBlock free (List.replicate count nameType ++ bound)
      (kept.map (liftBVars 0 count)) := by
    have lifted := Members.lift (language := ambientCoreCalc) (block := ambientBlock) (List.replicate count nameType)
      keptMembers
    rwa [List.length_replicate] at lifted
  have liftedBody : liftBVars 0 count (Prenex.body ambientBlock kept) =
      Prenex.body ambientBlock (kept.map (liftBVars 0 count)) := by
    rw [liftBVars_eq_rename, rename_body]
    congr 1
    exact List.map_congr_left fun pattern _ => (liftBVars_eq_rename 0 count pattern).symm
  have gathered : ProcEquiv ambientCoreCalc ambientBlock free (List.replicate count nameType ++ bound)
      (Prenex.body ambientBlock (kept.map (liftBVars 0 count) ++ moved))
      (Prenex.body ambientBlock
        (Prenex.body ambientBlock moved :: [Prenex.body ambientBlock kept].map (liftBVars 0 count))) := by
    rw [List.map_singleton, liftedBody]
    exact .trans _ _ _ (body_perm_equivalent (liftedMembers.append movedMembers) List.perm_append_comm)
      (Relation.EqvGen.symm _ _ (body_pair_equivalent movedMembers liftedMembers))
  refine .trans _ _ _ (restricts_congr (language := ambientCoreCalc) (block := ambientBlock) count gathered) ?_
  refine .trans _ _ _ (restricts_body_extract count (body_typed movedMembers)
    (Members.cons (body_typed keptMembers) Members.nil)) ?_
  exact body_pair_equivalent (Members.cons (restricts_typed (language := ambientCoreCalc) (block := ambientBlock) count
    (body_typed movedMembers)) Members.nil) keptMembers

/-- **Restrictions only one member of a body uses move onto it, in place**: `(νx̄){Ā↑ | P | B̄↑} ≡ {Ā | (νx̄)P | B̄}`. -/
theorem restricts_body_middle {bound : List TypeExpr} (count : Nat) {before after : List Pattern} {middle : Pattern}
    (beforeMembers : Members ambientCoreCalc ambientBlock free bound before)
    (afterMembers : Members ambientCoreCalc ambientBlock free bound after)
    (middleTyped : HasType ambientCoreCalc free (List.replicate count nameType ++ bound) middle procType) :
    ProcEquiv ambientCoreCalc ambientBlock free bound
      (Prenex.restricts ambientBlock count
        (Prenex.body ambientBlock (before.map (liftBVars 0 count) ++ middle :: after.map (liftBVars 0 count))))
      (Prenex.body ambientBlock (before ++ Prenex.restricts ambientBlock count middle :: after)) := by
  have keptMembers := beforeMembers.append afterMembers
  have liftedMembers : Members ambientCoreCalc ambientBlock free (List.replicate count nameType ++ bound)
      ((before ++ after).map (liftBVars 0 count)) := by
    have lifted := Members.lift (language := ambientCoreCalc) (block := ambientBlock) (List.replicate count nameType)
      keptMembers
    rwa [List.length_replicate] at lifted
  have permuted : (before.map (liftBVars 0 count) ++ middle :: after.map (liftBVars 0 count)).Perm
      ((before ++ after).map (liftBVars 0 count) ++ [middle]) := by
    rw [List.map_append]
    exact List.perm_middle.trans (List.perm_append_comm (l₁ := [middle]))
  have allMembers : Members ambientCoreCalc ambientBlock free (List.replicate count nameType ++ bound)
      (before.map (liftBVars 0 count) ++ middle :: after.map (liftBVars 0 count)) :=
    fun element member => (liftedMembers.append (Members.cons middleTyped Members.nil)) element
      (permuted.subset member)
  refine .trans _ _ _ (restricts_congr (language := ambientCoreCalc) (block := ambientBlock) count
    (body_perm_equivalent allMembers permuted)) ?_
  refine .trans _ _ _ (restricts_body_split count keptMembers (Members.cons middleTyped Members.nil)) ?_
  exact body_perm_equivalent (Members.cons (restricts_typed (language := ambientCoreCalc) (block := ambientBlock) count
    middleTyped) keptMembers) List.perm_middle.symm

/-! ## Reading beside a lifted copy group -/

theorem isVariable_lift (count : Nat) (pattern : Pattern) :
    isVariable (liftBVars 0 count pattern) = isVariable pattern := by
  rw [liftBVars_eq_rename, isVariable_rename]

/-- A component with a child is a marker, opened or not. -/
theorem childOf_eq_some {component child : Pattern} (isChild : childOf component = some child) :
    ∃ label parent name, label ∈ markers ∧ component = .apply label [parent, child, name] := by
  unfold childOf at isChild
  split at isChild
  · split_ifs at isChild with isMarker
    rw [Option.some.injEq] at isChild
    subst isChild
    exact ⟨_, _, _, isMarker, rfl⟩
  · cases isChild

/-- **A component whose ambients lead nowhere near a group reads as before, lifted**, beside the group. -/
theorem readComponent_lifted {owned : Nat} {home : Pattern} {group : List Pattern}
    (groupPlaced : ∀ component ∈ group, ∀ at', placeAt component = some at' →
      at' = liftBVars 0 owned home ∨ ∃ index < owned, at' = .bvar index)
    (fuel : Nat) (place component : Pattern) {rest : List Pattern}
    (apart : ∀ child, childOf component = some child → ¬ Reaches rest child home) :
    readComponent fuel (liftBVars 0 owned place) (liftBVars 0 owned component)
        (rest.map (liftBVars 0 owned) ++ group) =
      liftBVars 0 owned (readComponent fuel place component rest) := by
  have liftIs : liftBVars 0 owned = rename (shiftAbove 0 owned) := funext (liftBVars_eq_rename 0 owned)
  cases fuel with
  | zero => simp [readComponent, liftBVars]
  | succ fuel =>
      have dropped : readComponent (fuel + 1) (liftBVars 0 owned place) (liftBVars 0 owned component)
          (rest.map (liftBVars 0 owned) ++ group) =
          readComponent (fuel + 1) (liftBVars 0 owned place) (liftBVars 0 owned component)
            (rest.map (liftBVars 0 owned)) := by
        refine readComponent_congr fun child isChild => ?_
        rw [childOf_lift] at isChild
        cases found : childOf component with
        | none => rw [found] at isChild; cases isChild
        | some original =>
            rw [found, Option.map_some, Option.some.injEq] at isChild
            subst isChild
            refine readPlaced_unreached fuel _ _ _ fun other member at' isPlaced reached => ?_
            rcases reaches_lifted groupPlaced reached with ⟨deep, rfl, deeper⟩ | toHome
            · rcases groupPlaced other member _ isPlaced with same | ⟨index, below, isOwned⟩
              · rw [liftBVars_injective owned same] at deeper
                exact apart original found deeper
              · exact lift_ne_owned below isOwned
            · exact apart original found toHome
      rw [dropped, liftIs]
      exact (decode_rename (fuel + 1) (shiftAbove_injective 0 owned)).2.2 place component rest

/-! ## The three cases of the absorption -/

/-- **Nothing reached from the place reaches the copy group**: the group's restrictions are garbage. -/
theorem absorb_unreached {bound : List TypeExpr} {owned : Nat} {group : List Pattern} {home : Pattern}
    (groupPlaced : ∀ component ∈ group, ∀ at', placeAt component = some at' →
      at' = liftBVars 0 owned home ∨ ∃ index < owned, at' = .bvar index)
    (fuel : Nat) {place : Pattern} {others : List Pattern}
    (othersMembers : Members locatedCalc locatedBlock free bound others)
    (unreached : ¬ Reaches others place home) :
    ProcEquiv ambientCoreCalc ambientBlock free bound
      (Prenex.restricts ambientBlock owned (Prenex.body ambientBlock
        (readPlaced fuel (liftBVars 0 owned place) (others.map (liftBVars 0 owned) ++ group))))
      (Prenex.body ambientBlock (readPlaced fuel place others)) := by
  have liftIs : liftBVars 0 owned = rename (shiftAbove 0 owned) := funext (liftBVars_eq_rename 0 owned)
  have apart : ∀ component ∈ group, ∀ at', placeAt component = some at' →
      ¬ Reaches (others.map (liftBVars 0 owned) ++ group) (liftBVars 0 owned place) at' := by
    intro component member at' isPlaced reached
    rcases reaches_lifted groupPlaced reached with ⟨original, rfl, deeper⟩ | toHome
    · rcases groupPlaced component member _ isPlaced with same | ⟨index, below, isOwned⟩
      · rw [liftBVars_injective owned same] at deeper
        exact unreached deeper
      · exact lift_ne_owned below isOwned
    · exact unreached toHome
  rw [readPlaced_unreached fuel _ _ _ apart, liftIs,
    (decode_rename fuel (shiftAbove_injective 0 owned)).2.1 place others, ← rename_body, ← liftIs]
  exact restricts_lift_equivalent owned (body_typed ((decode_typed fuel).2.1 place others othersMembers))

/-- **The copy group sits at the place, beside its replication**: its restrictions move onto it, and the replication
absorbs what it reads as. -/
theorem absorb_here {bound : List TypeExpr} {owned : Nat} {group : List Pattern} {home argument : Pattern}
    (groupMembers : Members locatedCalc locatedBlock free (List.replicate owned nameType ++ bound) group)
    (groupPlaced : ∀ component ∈ group, ∀ at', placeAt component = some at' →
      at' = liftBVars 0 owned home ∨ ∃ index < owned, at' = .bvar index)
    (groupChildren : ∀ component ∈ group, ∀ child, childOf component = some child →
      ∃ index < owned, child = .bvar index)
    (fuel : Nat) {others : List Pattern}
    (othersMembers : Members locatedCalc locatedBlock free bound others)
    (replicated : .apply "LRep" [argument] ∈ others)
    (replicatedPlaced : placeAt (.apply "LRep" [argument]) = some home)
    (top : ∀ component ∈ others, childOf component ≠ some home)
    (copyEquiv : ProcEquiv ambientCoreCalc ambientBlock free bound
      (Prenex.restricts ambientBlock owned
        (Prenex.body ambientBlock (readPlaced (fuel + 2) (liftBVars 0 owned home) group)))
      (Prenex.toPattern ambientBlock (decodeForm fuel home (decompose locatedBlock argument)))) :
    ProcEquiv ambientCoreCalc ambientBlock free bound
      (Prenex.restricts ambientBlock owned (Prenex.body ambientBlock
        (readPlaced (fuel + 2) (liftBVars 0 owned home) (others.map (liftBVars 0 owned) ++ group))))
      (Prenex.body ambientBlock (readPlaced (fuel + 2) home others)) := by
  have liftIs : liftBVars 0 owned = rename (shiftAbove 0 owned) := funext (liftBVars_eq_rename 0 owned)
  have split : readPlaced (fuel + 2) (liftBVars 0 owned home) (others.map (liftBVars 0 owned) ++ group) =
      readPlaced (fuel + 2) (liftBVars 0 owned home) (others.map (liftBVars 0 owned)) ++
        readPlaced (fuel + 2) (liftBVars 0 owned home) group := by
    refine readPlaced_append (fuel + 2) _
      (firstReach := fun at' => ∃ original, at' = liftBVars 0 owned original ∧ original ≠ home)
      (secondReach := fun at' => ∃ index < owned, at' = .bvar index) ?_ groupChildren ?_ ?_
    · intro component member child isChild
      obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp member
      rw [childOf_lift] at isChild
      cases found : childOf original with
      | none => rw [found] at isChild; cases isChild
      | some originalChild =>
          rw [found, Option.map_some, Option.some.injEq] at isChild
          subst isChild
          exact ⟨originalChild, rfl, fun same => top original originalMember (by rw [found, same])⟩
    · rintro component member at' isPlaced ⟨original, rfl, different⟩
      rcases groupPlaced component member _ isPlaced with atLifted | ⟨index, below, isOwned⟩
      · exact different (liftBVars_injective owned atLifted)
      · exact lift_ne_owned below isOwned
    · rintro component member at' isPlaced ⟨index, below, rfl⟩
      obtain ⟨original, -, rfl⟩ := List.mem_map.mp member
      rw [liftIs, placeAt_rename] at isPlaced
      cases found : placeAt original with
      | none => rw [found] at isPlaced; cases isPlaced
      | some originalAt =>
          rw [found, Option.map_some, Option.some.injEq, ← liftIs] at isPlaced
          exact lift_ne_owned below isPlaced
  have renamed : readPlaced (fuel + 2) (liftBVars 0 owned home) (others.map (liftBVars 0 owned)) =
      (readPlaced (fuel + 2) home others).map (liftBVars 0 owned) := by
    rw [liftIs]
    exact (decode_rename (fuel + 2) (shiftAbove_injective 0 owned)).2.1 home others
  have readingTyped : Members ambientCoreCalc ambientBlock free bound (readPlaced (fuel + 2) home others) :=
    (decode_typed (fuel + 2)).2.1 home others othersMembers
  have groupTyped : Members ambientCoreCalc ambientBlock free (List.replicate owned nameType ++ bound)
      (readPlaced (fuel + 2) (liftBVars 0 owned home) group) :=
    (decode_typed (fuel + 2)).2.1 _ group groupMembers
  rw [split, renamed]
  refine .trans _ _ _ (restricts_body_split owned readingTyped groupTyped) ?_
  have signature : BlockSignature locatedCalc locatedBlock := locatedLanguage.toBlockSignature
  obtain ⟨argumentMembers, -⟩ := decompose_sound (language := locatedCalc) (block := locatedBlock)
    (rep_inv (othersMembers _ replicated))
  have copyTyped := decodeForm_typed (free := free) (bound := bound) fuel home argumentMembers
  refine .trans _ _ _ (body_congr (Members.cons (restricts_typed (language := ambientCoreCalc) (block := ambientBlock)
    owned (body_typed groupTyped)) readingTyped) (.cons copyEquiv (forall₂_self (fun _ => .refl _) _))) ?_
  refine absorb_body copyTyped readingTyped ?_
  rw [readPlaced_succ]
  refine List.mem_map.mpr ⟨_, List.mem_filter.mpr ⟨replicated, by simp [placedAt, replicatedPlaced]⟩, ?_⟩
  simp [readComponent]

/-- **The copy group sits below one ambient at the place**: every other component there reads as before, lifted, and
the group's restrictions move into that ambient. -/
theorem absorb_below {bound : List TypeExpr} {owned : Nat} {group : List Pattern} {home : Pattern}
    {label : String} (isMarker : label ∈ markers)
    (groupMembers : Members locatedCalc locatedBlock free (List.replicate owned nameType ++ bound) group)
    (groupPlaced : ∀ component ∈ group, ∀ at', placeAt component = some at' →
      at' = liftBVars 0 owned home ∨ ∃ index < owned, at' = .bvar index)
    (fuel : Nat) {place child name : Pattern} {others : List Pattern}
    (othersMembers : Members locatedCalc locatedBlock free bound others)
    (different : home ≠ place)
    (marked : .apply label [place, child, name] ∈ others)
    (leads : Reaches (others.filter fun other => !placedAt place other) child home)
    (unique : ∀ child, (others.filter fun component => childOf component == some child).length ≤ 1)
    (nameVariable : isVariable name = true)
    (inner : ProcEquiv ambientCoreCalc ambientBlock free bound
      (Prenex.restricts ambientBlock owned (Prenex.body ambientBlock (readPlaced fuel (liftBVars 0 owned child)
        ((others.filter fun other => !placedAt place other).map (liftBVars 0 owned) ++ group))))
      (Prenex.body ambientBlock (readPlaced fuel child (others.filter fun other => !placedAt place other)))) :
    ProcEquiv ambientCoreCalc ambientBlock free bound
      (Prenex.restricts ambientBlock owned (Prenex.body ambientBlock
        (readPlaced (fuel + 2) (liftBVars 0 owned place) (others.map (liftBVars 0 owned) ++ group))))
      (Prenex.body ambientBlock (readPlaced (fuel + 2) place others)) := by
  have markerPlaced : placedAt place (.apply label [place, child, name]) = true := by
    simp [placedAt, placeAt_ofMarker isMarker]
  have markerHere : .apply label [place, child, name] ∈ others.filter (placedAt place) :=
    List.mem_filter.mpr ⟨marked, markerPlaced⟩
  obtain ⟨before, after, splitIs⟩ := List.append_of_mem markerHere
  have besides : ∀ other ∈ before ++ after, (childOf other == some child) = false := by
    have sub : (before ++ .apply label [place, child, name] :: after).Sublist others := by
      rw [← splitIs]
      exact List.filter_sublist
    exact unkept_beside sub (unique child) (by simp [childOf_ofMarker isMarker])
  have patternUnique : ∀ first ∈ others, ∀ second ∈ others, ∀ child, childOf first = some child →
      childOf second = some child → first = second :=
    fun first firstIn second secondIn child firstChild secondChild =>
      eq_of_filter_length_le_one (unique child) firstIn secondIn (by simp [firstChild]) (by simp [secondChild])
  have inOthers : ∀ other ∈ before ++ after, other ∈ others.filter (placedAt place) := by
    intro other member
    rw [splitIs]
    rcases List.mem_append.mp member with inBefore | inAfter
    · exact List.mem_append_left _ inBefore
    · exact List.mem_append_right _ (List.mem_cons_of_mem _ inAfter)
  have liftedItem : ∀ other ∈ before ++ after,
      readComponent (fuel + 1) (liftBVars 0 owned place) (liftBVars 0 owned other)
        ((others.filter fun other => !placedAt place other).map (liftBVars 0 owned) ++ group) =
      liftBVars 0 owned (readComponent (fuel + 1) place other (others.filter fun other => !placedAt place other)) := by
    intro other member
    refine readComponent_lifted groupPlaced (fuel + 1) place other fun otherChild isChild reachedOther => ?_
    obtain ⟨otherMember, otherPlaced⟩ := List.mem_filter.mp (inOthers other member)
    obtain ⟨steps, reachedSteps⟩ := leads.steps
    have same := reaches_unique patternUnique (fun _ member => member) steps reachedSteps reachedOther
      ⟨_, marked, markerPlaced, childOf_ofMarker isMarker _ _ _⟩ ⟨other, otherMember, otherPlaced, isChild⟩
    have unmarked := besides other member
    rw [isChild, ← same] at unmarked
    simp at unmarked
  have groupNotHere : ∀ component ∈ group, placedAt (liftBVars 0 owned place) component = false := by
    intro component member
    cases found : placeAt component with
    | none => simp [placedAt, found]
    | some at' =>
        simp only [placedAt, found, beq_eq_false_iff_ne, ne_eq, Option.some.injEq]
        rcases groupPlaced component member at' found with same | ⟨index, below, isOwned⟩
        · rw [same]
          exact fun equal => different (liftBVars_injective owned equal)
        · rw [isOwned]
          exact fun equal => lift_ne_owned below equal.symm
  have liftedHere : (others.map (liftBVars 0 owned) ++ group).filter (placedAt (liftBVars 0 owned place)) =
      (others.filter (placedAt place)).map (liftBVars 0 owned) := by
    have groupEmpty : group.filter (placedAt (liftBVars 0 owned place)) = [] :=
      List.filter_eq_nil_iff.mpr fun component member isPlaced => by
        rw [groupNotHere component member] at isPlaced
        cases isPlaced
    rw [List.filter_append, groupEmpty, List.append_nil, List.filter_map]
    congr 1
    exact List.filter_congr fun other _ => by simp [placedAt_lift]
  have liftedElsewhere : (others.map (liftBVars 0 owned) ++ group).filter
      (fun other => !placedAt (liftBVars 0 owned place) other) =
      (others.filter fun other => !placedAt place other).map (liftBVars 0 owned) ++ group := by
    have groupAll : group.filter (fun other => !placedAt (liftBVars 0 owned place) other) = group :=
      List.filter_eq_self.mpr fun component member => by simp [groupNotHere component member]
    rw [List.filter_append, groupAll, List.filter_map]
    congr 2
    exact List.filter_congr fun other _ => by simp [placedAt_lift]
  have markerItem : readComponent (fuel + 1) (liftBVars 0 owned place)
      (liftBVars 0 owned (.apply label [place, child, name]))
      ((others.filter fun other => !placedAt place other).map (liftBVars 0 owned) ++ group) =
      wrapContent label (liftBVars 0 owned name) (Prenex.body ambientBlock (readPlaced fuel
        (liftBVars 0 owned child) ((others.filter fun other => !placedAt place other).map (liftBVars 0 owned) ++
          group))) := by
    simp [liftBVars, readComponent, isVariable_lift, nameVariable, isMarker]
  have rightItem : readComponent (fuel + 1) place (.apply label [place, child, name])
      (others.filter fun other => !placedAt place other) =
      wrapContent label name (Prenex.body ambientBlock (readPlaced fuel child
        (others.filter fun other => !placedAt place other))) := by
    simp [readComponent, nameVariable, isMarker]
  have itemsLeft : readPlaced (fuel + 2) (liftBVars 0 owned place) (others.map (liftBVars 0 owned) ++ group) =
      (before.map fun other => readComponent (fuel + 1) place other
          (others.filter fun other => !placedAt place other)).map (liftBVars 0 owned) ++
        wrapContent label (liftBVars 0 owned name) (Prenex.body ambientBlock (readPlaced fuel
          (liftBVars 0 owned child) ((others.filter fun other => !placedAt place other).map (liftBVars 0 owned) ++
            group))) ::
        (after.map fun other => readComponent (fuel + 1) place other
          (others.filter fun other => !placedAt place other)).map (liftBVars 0 owned) := by
    rw [readPlaced_succ, liftedHere, liftedElsewhere, splitIs]
    simp only [List.map_map, List.map_append, List.map_cons]
    refine congrArg₂ (· ++ ·) ?_ (congrArg₂ List.cons markerItem ?_)
    · exact List.map_congr_left fun other member => liftedItem other (List.mem_append_left _ member)
    · exact List.map_congr_left fun other member => liftedItem other (List.mem_append_right _ member)
  have itemsRight : readPlaced (fuel + 2) place others =
      (before.map fun other => readComponent (fuel + 1) place other
          (others.filter fun other => !placedAt place other)) ++
        wrapContent label name (Prenex.body ambientBlock (readPlaced fuel child
          (others.filter fun other => !placedAt place other))) ::
        (after.map fun other => readComponent (fuel + 1) place other
          (others.filter fun other => !placedAt place other)) := by
    rw [readPlaced_succ, splitIs]
    simp only [List.map_append, List.map_cons, rightItem]
  have restMembers : Members locatedCalc locatedBlock free bound (others.filter fun other => !placedAt place other) :=
    fun element member => othersMembers element (List.mem_filter.mp member).1
  have liftedRest : Members locatedCalc locatedBlock free (List.replicate owned nameType ++ bound)
      ((others.filter fun other => !placedAt place other).map (liftBVars 0 owned) ++ group) := by
    have lifted := Members.lift (language := locatedCalc) (block := locatedBlock) (List.replicate owned nameType)
      restMembers
    rw [List.length_replicate] at lifted
    exact lifted.append groupMembers
  have sideMembers : ∀ side : List Pattern, (∀ other ∈ side, other ∈ before ++ after) →
      Members ambientCoreCalc ambientBlock free bound (side.map fun other => readComponent (fuel + 1) place other
        (others.filter fun other => !placedAt place other)) := by
    intro side within element member
    obtain ⟨other, otherIn, rfl⟩ := List.mem_map.mp member
    exact (decode_typed (fuel + 1)).2.2 place other _
      (othersMembers other (List.mem_filter.mp (inOthers other (within other otherIn))).1) restMembers
  have beforeMembers := sideMembers before fun other member => List.mem_append_left _ member
  have afterMembers := sideMembers after fun other member => List.mem_append_right _ member
  have nameTyped : HasType ambientCoreCalc free bound name nameType := by
    rcases triple_inv (othersMembers _ marked) with ⟨-, -, typed⟩ | ⟨listed, -, -⟩ | ⟨rfl, -, -⟩
    · exact variable_typed typed nameVariable
    · exact absurd listed (not_capability_of_marker isMarker)
    · simp [markers] at isMarker
  have liftedName : HasType ambientCoreCalc free (List.replicate owned nameType ++ bound) (liftBVars 0 owned name)
      nameType := by
    simpa using lift_typed (language := ambientCoreCalc) (inner := []) (inserted := List.replicate owned nameType)
      (outer := bound) nameTyped
  have bodyTyped : HasType ambientCoreCalc free (List.replicate owned nameType ++ bound)
      (Prenex.body ambientBlock (readPlaced fuel (liftBVars 0 owned child)
        ((others.filter fun other => !placedAt place other).map (liftBVars 0 owned) ++ group))) procType :=
    body_typed ((decode_typed fuel).2.1 _ _ liftedRest)
  have markerTyped := wrapContent_typed label liftedName bodyTyped
  rw [itemsLeft, itemsRight]
  refine .trans _ _ _ (restricts_body_middle owned beforeMembers afterMembers markerTyped) ?_
  refine body_congr (beforeMembers.append (Members.cons (restricts_typed (language := ambientCoreCalc)
    (block := ambientBlock) owned markerTyped) afterMembers)) (forall₂_middle (fun _ => .refl _) ?_ _ _)
  exact .trans _ _ _ (restricts_wrapContent_equivalent label owned nameTyped bodyTyped)
    (wrapContent_fill label nameTyped inner)

/-- **A copy group read beside its replication is absorbed, at any depth**: reading from a place, the group's
restrictions over the lifted components and the group read as the components alone, when the group reads, at the
replication's place, as the replication's argument. -/
theorem absorb_core {bound : List TypeExpr} {owned least : Nat} {group : List Pattern} {home argument : Pattern}
    (groupMembers : Members locatedCalc locatedBlock free (List.replicate owned nameType ++ bound) group)
    (groupPlaced : ∀ component ∈ group, ∀ at', placeAt component = some at' →
      at' = liftBVars 0 owned home ∨ ∃ index < owned, at' = .bvar index)
    (groupChildren : ∀ component ∈ group, ∀ child, childOf component = some child →
      ∃ index < owned, child = .bvar index)
    (copyEquiv : ∀ fuel, least ≤ fuel → ProcEquiv ambientCoreCalc ambientBlock free bound
      (Prenex.restricts ambientBlock owned
        (Prenex.body ambientBlock (readPlaced (fuel + 2) (liftBVars 0 owned home) group)))
      (Prenex.toPattern ambientBlock (decodeForm fuel home (decompose locatedBlock argument)))) :
    ∀ (fuel : Nat) {place : Pattern} {others : List Pattern},
      Members locatedCalc locatedBlock free bound others →
      .apply "LRep" [argument] ∈ others → placeAt (.apply "LRep" [argument]) = some home →
      (∀ component ∈ others, childOf component ≠ some place) →
      (∀ child, (others.filter fun component => childOf component == some child).length ≤ 1) →
      (∀ component ∈ others, ∀ name, nameOf component = some name → isVariable name = true) →
      least + 2 + 2 * others.length ≤ fuel →
      ProcEquiv ambientCoreCalc ambientBlock free bound
        (Prenex.restricts ambientBlock owned (Prenex.body ambientBlock
          (readPlaced fuel (liftBVars 0 owned place) (others.map (liftBVars 0 owned) ++ group))))
        (Prenex.body ambientBlock (readPlaced fuel place others))
  | 0, _, _, _, _, _, _, _, _, enough => by omega
  | 1, _, _, _, _, _, _, _, _, enough => by omega
  | fuel + 2, place, others, othersMembers, replicated, replicatedPlaced, top, unique, namesVariable, enough => by
      by_cases atHome : home = place
      · subst atHome
        exact absorb_here groupMembers groupPlaced groupChildren fuel othersMembers replicated replicatedPlaced top
          (copyEquiv fuel (by omega))
      · by_cases reached : Reaches others place home
        · obtain ⟨marker, markerMember, markerPlaced, child, markerChild, below⟩ :
              ∃ marker ∈ others, placedAt place marker = true ∧ ∃ child, childOf marker = some child ∧
                Reaches (others.filter fun other => !placedAt place other) child home := by
            cases reached with
            | here => exact absurd rfl atHome
            | down markerMember markerPlaced markerChild below =>
                exact ⟨_, markerMember, markerPlaced, _, markerChild, below⟩
          obtain ⟨label, parent, name, isMarker, markerIs⟩ := childOf_eq_some markerChild
          have parentIs : parent = place := by
            rw [markerIs] at markerPlaced
            simpa [placedAt, placeAt_ofMarker isMarker] using markerPlaced
          rw [parentIs] at markerIs
          subst markerIs
          have nameVariable : isVariable name = true :=
            namesVariable _ markerMember name (by simp [nameOf, isMarker])
          have restLength : (others.filter fun other => !placedAt place other).length + 1 ≤ others.length := by
            have total := List.length_eq_length_filter_add (l := others) (placedAt place)
            have positive := List.length_pos_of_mem (List.mem_filter.mpr ⟨markerMember, markerPlaced⟩)
            omega
          refine absorb_below isMarker groupMembers groupPlaced fuel othersMembers atHome markerMember below unique
            nameVariable ?_
          refine absorb_core groupMembers groupPlaced groupChildren copyEquiv fuel
            (fun element member => othersMembers element (List.mem_filter.mp member).1)
            (List.mem_filter.mpr ⟨replicated, by simp [placedAt, replicatedPlaced, atHome]⟩) replicatedPlaced
            ?_ ?_ ?_ (by omega)
          · intro component member isChild
            obtain ⟨inOthers, notHere⟩ := List.mem_filter.mp member
            have same := eq_of_filter_length_le_one (unique child) inOthers markerMember (by simp [isChild])
              (by simp [childOf_ofMarker isMarker])
            subst same
            simp [markerPlaced] at notHere
          · intro child'
            exact le_trans (List.Sublist.filter _ List.filter_sublist).length_le (unique child')
          · intro component member
            exact namesVariable component (List.mem_filter.mp member).1
        · exact absorb_unreached groupPlaced (fuel + 2) othersMembers reached

end Mettapedia.Languages.ProcessCalculi.Ambient.Decoding
