import Mettapedia.Languages.ProcessCalculi.Ambient.DecodingRename

/-!
# Reading back blocks side by side

Reading back at a place reads only the components placed at the places it reaches through markers
(`readPlaced_congr`). A block is **rooted** at a place when every component sits at that place or at one of the
block's own restrictions, and every marker places its ambient at one of them (`Rooted`). Two rooted blocks side by side
read back as their readings side by side (`decodeForm_par`): neither reaches the other's restrictions.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.Ambient.Decoding

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Substitution (liftBVars)
open Mettapedia.OSLF.MeTTaIL.CanonicalBags (liftIndex)
open Mettapedia.GSLT.LanguageDef.RestrictionBlocks (Prenex decompose rename rename_bvar rename_comp liftBVars_eq_rename
  shiftAbove)
open Mettapedia.Languages.ProcessCalculi.Ambient.Full (ambientBlock)
open Mettapedia.Languages.ProcessCalculi.Ambient.Located (locatedBlock)

/-! ## What reading at a place reads -/

/-- The location a marker places its ambient at, opened or not. -/
def childOf : Pattern → Option Pattern
  | .apply label [_, child, _] => if label ∈ markers then some child else none
  | _ => none

theorem readPlaced_succ (fuel : Nat) (place : Pattern) (components : List Pattern) :
    readPlaced (fuel + 1) place components =
      (components.filter (placedAt place)).map fun component =>
        readComponent fuel place component (components.filter fun other => !placedAt place other) := rfl

/-- What sits at another place among the components placed elsewhere. -/
theorem filter_elsewhere (place other : Pattern) (components : List Pattern) :
    (components.filter fun component => !placedAt place component).filter (placedAt other) =
      if other = place then [] else components.filter (placedAt other) := by
  split_ifs with same
  · subst same
    rw [List.filter_filter, List.filter_eq_nil_iff]
    intro component _
    simp
  · rw [List.filter_filter]
    congr 1
    funext component
    by_cases there : placedAt other component = true
    · have notHere : placedAt place component = false := by
        have sits : placeAt component = some other := by simpa [placedAt] using there
        simp [placedAt, sits, same]
      simp [there, notHere]
    · simp [there]

/-- A component other than a marker is read without the others. -/
theorem readComponent_congr {fuel : Nat} {place component : Pattern} {first second : List Pattern}
    (children : ∀ child, childOf component = some child → readPlaced fuel child first = readPlaced fuel child second) :
    readComponent (fuel + 1) place component first = readComponent (fuel + 1) place component second := by
  cases component with
  | apply label arguments =>
      match arguments, children with
      | [_, child, _], children =>
          simp only [readComponent]
          split_ifs with isMarker
          · rw [children child (by simp [childOf, isMarker])]
          all_goals rfl
      | [], _ => rfl
      | [_], _ => rfl
      | [_, _], _ => rfl
      | _ :: _ :: _ :: _ :: _, _ => rfl
  | _ => rfl

/-- **Reading at a place reads only what sits where it reaches**: two lists with the same components at every place
of a reach closed under the markers' locations read alike at every place of the reach. -/
theorem readPlaced_congr : ∀ (fuel : Nat) {reach : Pattern → Prop} {first second : List Pattern},
    (∀ place, reach place → first.filter (placedAt place) = second.filter (placedAt place)) →
    (∀ component ∈ first, ∀ place, reach place → placedAt place component = true →
      ∀ child, childOf component = some child → reach child) →
    ∀ place, reach place → readPlaced fuel place first = readPlaced fuel place second
  | 0, _, _, _, _, _, _, _ => rfl
  | fuel + 1, reach, first, second, same, closed, place, reached => by
      rw [readPlaced_succ, readPlaced_succ, ← same place reached]
      refine List.map_congr_left fun component member => ?_
      obtain ⟨inFirst, isPlaced⟩ := List.mem_filter.mp member
      cases fuel with
      | zero => rfl
      | succ fuel =>
          refine readComponent_congr fun child isChild => readPlaced_congr fuel (fun at' reached' => ?_)
            (fun other inRest at' reached' otherPlaced grandchild isGrandchild => ?_) child
            (closed component inFirst place reached isPlaced child isChild)
          · rw [filter_elsewhere, filter_elsewhere]
            split_ifs
            · rfl
            · exact same at' reached'
          · exact closed other (List.mem_filter.mp inRest).1 at' reached' otherPlaced grandchild isGrandchild

/-! ## Rooted blocks -/

/-- **A block rooted at a place**: every component sits at the place, read inside the block, or at one of the block's
restrictions, and every marker places its ambient at one of the block's restrictions. -/
structure Rooted (place : Pattern) (form : Prenex) : Prop where
  placed : ∀ component ∈ form.components, ∀ at', placeAt component = some at' →
    at' = liftBVars 0 form.count place ∨ ∃ index < form.count, at' = .bvar index
  children : ∀ component ∈ form.components, ∀ child, childOf component = some child →
    ∃ index < form.count, child = .bvar index

theorem childOf_rename (relabel : Nat → Nat) (component : Pattern) :
    childOf (rename relabel component) = (childOf component).map (rename relabel) := by
  cases component with
  | apply label arguments =>
      match arguments with
      | [_, _, _] =>
          simp only [Mettapedia.GSLT.LanguageDef.RestrictionBlocks.rename_apply, List.map_cons, List.map_nil, childOf]
          split_ifs <;> rfl
      | [] => simp [Mettapedia.GSLT.LanguageDef.RestrictionBlocks.rename_apply, childOf]
      | [_] => simp [Mettapedia.GSLT.LanguageDef.RestrictionBlocks.rename_apply, childOf]
      | [_, _] => simp [Mettapedia.GSLT.LanguageDef.RestrictionBlocks.rename_apply, childOf]
      | _ :: _ :: _ :: _ :: _ => simp [Mettapedia.GSLT.LanguageDef.RestrictionBlocks.rename_apply, childOf]
  | _ => simp [rename_bvar, Mettapedia.GSLT.LanguageDef.RestrictionBlocks.rename_fvar,
      Mettapedia.GSLT.LanguageDef.RestrictionBlocks.rename_lambda,
      Mettapedia.GSLT.LanguageDef.RestrictionBlocks.rename_multiLambda,
      Mettapedia.GSLT.LanguageDef.RestrictionBlocks.rename_subst,
      Mettapedia.GSLT.LanguageDef.RestrictionBlocks.rename_collection, childOf]

/-! ## Blocks side by side -/

/-- **Two lists that reach apart read side by side**: each list's markers place ambients in its own reach, which no
component of the other sits in. -/
theorem readPlaced_append (fuel : Nat) (place : Pattern) {first second : List Pattern}
    {firstReach secondReach : Pattern → Prop}
    (firstClosed : ∀ component ∈ first, ∀ child, childOf component = some child → firstReach child)
    (secondClosed : ∀ component ∈ second, ∀ child, childOf component = some child → secondReach child)
    (firstApart : ∀ component ∈ second, ∀ at', placeAt component = some at' → ¬ firstReach at')
    (secondApart : ∀ component ∈ first, ∀ at', placeAt component = some at' → ¬ secondReach at') :
    readPlaced fuel place (first ++ second) = readPlaced fuel place first ++ readPlaced fuel place second := by
  cases fuel with
  | zero => rfl
  | succ fuel =>
      have noneAt : ∀ {reach : Pattern → Prop} {others : List Pattern},
          (∀ component ∈ others, ∀ at', placeAt component = some at' → ¬ reach at') →
          ∀ at', reach at' → others.filter (placedAt at') = [] := by
        intro reach others apart at' reached
        rw [List.filter_eq_nil_iff]
        intro component member isPlaced
        exact apart component member at' (by simpa [placedAt] using isPlaced) reached
      rw [readPlaced_succ, readPlaced_succ, readPlaced_succ]
      simp only [List.filter_append, List.map_append]
      congr 1
      · refine List.map_congr_left fun component member => ?_
        cases fuel with
        | zero => rfl
        | succ fuel =>
            obtain ⟨inFirst, -⟩ := List.mem_filter.mp member
            refine readComponent_congr fun child isChild => ?_
            refine readPlaced_congr fuel (reach := firstReach) (fun at' reached => ?_) (fun other inRest at' reached
              isPlaced grandchild isGrandchild => ?_) child (firstClosed component inFirst child isChild)
            · have nothing : (second.filter fun other => !placedAt place other).filter (placedAt at') = [] := by
                rw [List.filter_eq_nil_iff]
                intro other inRest otherPlaced
                exact firstApart other (List.mem_filter.mp inRest).1 at' (by simpa [placedAt] using otherPlaced)
                  reached
              rw [List.filter_append, nothing, List.append_nil]
            · rcases List.mem_append.mp inRest with inFirst' | inSecond
              · exact firstClosed other (List.mem_filter.mp inFirst').1 grandchild isGrandchild
              · exact absurd reached (firstApart other (List.mem_filter.mp inSecond).1 at'
                  (by simpa [placedAt] using isPlaced))
      · refine List.map_congr_left fun component member => ?_
        cases fuel with
        | zero => rfl
        | succ fuel =>
            obtain ⟨inSecond, -⟩ := List.mem_filter.mp member
            refine readComponent_congr fun child isChild => ?_
            refine readPlaced_congr fuel (reach := secondReach) (fun at' reached => ?_) (fun other inRest at' reached
              isPlaced grandchild isGrandchild => ?_) child (secondClosed component inSecond child isChild)
            · have nothing : (first.filter fun other => !placedAt place other).filter (placedAt at') = [] := by
                rw [List.filter_eq_nil_iff]
                intro other inRest otherPlaced
                exact secondApart other (List.mem_filter.mp inRest).1 at' (by simpa [placedAt] using otherPlaced)
                  reached
              rw [List.filter_append, nothing, List.nil_append]
            · rcases List.mem_append.mp inRest with inFirst | inSecond'
              · exact absurd reached (secondApart other (List.mem_filter.mp inFirst).1 at'
                  (by simpa [placedAt] using isPlaced))
              · exact secondClosed other (List.mem_filter.mp inSecond').1 grandchild isGrandchild

theorem shiftAbove_injective (cutoff shift : Nat) : Function.Injective (shiftAbove cutoff shift) := by
  intro first second same
  simp only [shiftAbove] at same
  split_ifs at same <;> omega

theorem liftBVars_par_outer (first second : Nat) (place : Pattern) :
    liftBVars 0 second (liftBVars 0 first place) = liftBVars 0 (first + second) place := by
  rw [liftBVars_eq_rename, liftBVars_eq_rename, liftBVars_eq_rename, rename_comp]
  congr 1
  funext index
  simp [Function.comp, shiftAbove]
  omega

theorem liftBVars_par_inner (first second : Nat) (place : Pattern) :
    liftBVars second first (liftBVars 0 second place) = liftBVars 0 (first + second) place := by
  rw [liftBVars_eq_rename, liftBVars_eq_rename, liftBVars_eq_rename, rename_comp]
  congr 1
  funext index
  simp only [Function.comp, shiftAbove, Nat.not_lt_zero, if_false]
  split_ifs <;> omega

/-- **Rooted blocks side by side read back side by side.** -/
theorem decodeForm_par (fuel : Nat) (place : Pattern) {first second : Prenex}
    (firstRooted : Rooted place first) (secondRooted : Rooted place second) :
    decodeForm (fuel + 1) place (first.par second) =
      (decodeForm (fuel + 1) place first).par (decodeForm (fuel + 1) place second) := by
  obtain ⟨outer, firstComponents⟩ := first
  obtain ⟨inner, secondComponents⟩ := second
  obtain ⟨firstPlaced, firstChildren⟩ := firstRooted
  obtain ⟨secondPlaced, secondChildren⟩ := secondRooted
  simp only at firstPlaced firstChildren secondPlaced secondChildren
  have firstInjective := shiftAbove_injective 0 inner
  have secondInjective := shiftAbove_injective inner outer
  have firstRead := (decode_rename fuel firstInjective).2.1 (liftBVars 0 outer place) firstComponents
  have secondRead := (decode_rename fuel secondInjective).2.1 (liftBVars 0 inner place) secondComponents
  have liftIs : ∀ cutoff shift, rename (shiftAbove cutoff shift) = liftBVars cutoff shift :=
    fun cutoff shift => funext fun pattern => (liftBVars_eq_rename cutoff shift pattern).symm
  simp only [decodeForm, Prenex.par, Prenex.mk.injEq, true_and]
  simp only [liftIs] at firstRead secondRead
  rw [liftBVars_par_outer] at firstRead
  rw [liftBVars_par_inner] at secondRead
  rw [← firstRead, ← secondRead]
  refine readPlaced_append fuel _ (firstReach := fun at' => ∃ index, inner ≤ index ∧ index < outer + inner ∧
      at' = .bvar index) (secondReach := fun at' => ∃ index < inner, at' = .bvar index) ?_ ?_ ?_ ?_
  · intro component member child isChild
    obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp member
    rw [liftBVars_eq_rename, childOf_rename] at isChild
    cases found : childOf original with
    | none => rw [found] at isChild; cases isChild
    | some originalChild =>
        rw [found, Option.map_some, Option.some.injEq] at isChild
        obtain ⟨index, below, rfl⟩ := firstChildren original originalMember originalChild found
        subst isChild
        exact ⟨index + inner, by omega, by omega, by simp [rename_bvar, shiftAbove]⟩
  · intro component member child isChild
    obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp member
    rw [liftBVars_eq_rename, childOf_rename] at isChild
    cases found : childOf original with
    | none => rw [found] at isChild; cases isChild
    | some originalChild =>
        rw [found, Option.map_some, Option.some.injEq] at isChild
        obtain ⟨index, below, rfl⟩ := secondChildren original originalMember originalChild found
        subst isChild
        exact ⟨index, below, by simp [rename_bvar, shiftAbove, below]⟩
  · intro component member at' isPlaced reached
    obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp member
    rw [liftBVars_eq_rename, placeAt_rename] at isPlaced
    cases found : placeAt original with
    | none => rw [found] at isPlaced; cases isPlaced
    | some originalPlace =>
        rw [found, Option.map_some, Option.some.injEq] at isPlaced
        obtain ⟨index, low, high, rfl⟩ := reached
        rcases secondPlaced original originalMember originalPlace found with rfl | ⟨inside, below, rfl⟩
        · rw [← liftBVars_eq_rename, liftBVars_par_inner] at isPlaced
          cases place with
          | bvar outerIndex =>
              simp [liftBVars] at isPlaced
              omega
          | fvar => simp [liftBVars] at isPlaced
          | _ => simp [liftBVars] at isPlaced
        · simp only [rename_bvar, shiftAbove, below, if_true, Pattern.bvar.injEq] at isPlaced
          omega
  · intro component member at' isPlaced reached
    obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp member
    rw [liftBVars_eq_rename, placeAt_rename] at isPlaced
    cases found : placeAt original with
    | none => rw [found] at isPlaced; cases isPlaced
    | some originalPlace =>
        rw [found, Option.map_some, Option.some.injEq] at isPlaced
        obtain ⟨index, below, rfl⟩ := reached
        rcases firstPlaced original originalMember originalPlace found with rfl | ⟨inside, insideBelow, rfl⟩
        · rw [← liftBVars_eq_rename, liftBVars_par_outer] at isPlaced
          cases place with
          | bvar outerIndex =>
              simp [liftBVars] at isPlaced
              omega
          | fvar => simp [liftBVars] at isPlaced
          | _ => simp [liftBVars] at isPlaced
        · simp only [rename_bvar, shiftAbove, Nat.not_lt_zero, if_false, Pattern.bvar.injEq] at isPlaced
          omega

end Mettapedia.Languages.ProcessCalculi.Ambient.Decoding
