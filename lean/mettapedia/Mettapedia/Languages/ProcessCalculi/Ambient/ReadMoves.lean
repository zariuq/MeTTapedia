import Mettapedia.Languages.ProcessCalculi.Ambient.ReadReactions

/-!
# Reading a move back as a step

An entry or an exit of a located redex, read at the place the reaction happens, is a step there: the ambients its
three parts read as step to what the reacted components read as, under the continuation's restrictions. Entering
reads at the place both ambients sit at; the moved ambient's marker leaves that place for the target's location.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.Ambient.Steps

open Mettapedia.Languages.ProcessCalculi.Ambient.Comm (ambientCoreCalc coreSignature)

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Substitution (liftBVars)
open Mettapedia.GSLT.LanguageDef.WellSorted (HasType FreeTypeContext isObjectPattern)
open Mettapedia.GSLT.LanguageDef.RestrictionBlocks (Prenex Members ProcEquiv sizeList size body_congr
  body_perm_equivalent bag_body_equivalent restricts_typed body_typed decompose restricts_congr body_pair_equivalent)
open Mettapedia.Languages.ProcessCalculi.Ambient.Full (AmbNuRawStep ambientBlock amb_fill amb_typed)
open Mettapedia.Languages.ProcessCalculi.Ambient.Located (locatedCalc locatedBlock)
open Mettapedia.Languages.ProcessCalculi.Ambient.Mobile (amb)
open Mettapedia.GSLT.LanguageDef.BagNormalForm (elementsHaveType_iff)
open Mettapedia.Languages.ProcessCalculi.Ambient.Encoding (nameType procType)
open Mettapedia.Languages.ProcessCalculi.Ambient.Decoding (isVariable Reaches placedAt placeAt childOf readPlaced
  readComponent readPlaced_succ markers capabilities ambientCapability decodeForm placeAt_ofMarker placeAt_capability
  liftBVars_injective lift_ne_owned placedAt_lift isVariable_lift size_pos size_le_sizeList size_add_elsewhere
  decodeForm_settled decodeForm_typed decode_typed decode_object eq_of_filter_length_le_one triple_inv variable_typed
  restricts_body_middle restricts_amb_equivalent restricts_body_split)

variable {free : FreeTypeContext}

/-! ## No place lies below itself -/

/-- **A marker's location does not reach back to where it sits.** -/
theorem not_reaches_up {count : Nat} {components : List Pattern} {depth : Nat → Nat}
    (children : ∀ component ∈ components, ∀ child, childOf component = some child →
      ∃ index < count, child = .bvar index)
    (grows : ∀ component ∈ components, ∀ index child, index < count → child < count →
      placeAt component = some (.bvar index) → childOf component = some (.bvar child) → depth index < depth child)
    {list : List Pattern} (within : ∀ component ∈ list, component ∈ components) {component place child : Pattern}
    (member : component ∈ components) (isPlaced : placeAt component = some place)
    (isChild : childOf component = some child) : ¬ Reaches list child place := by
  intro back
  obtain ⟨index, below, rfl⟩ := children component member child isChild
  by_cases same : Pattern.bvar index = place
  · subst same
    have := grows component member index index below below isPlaced isChild
    omega
  · obtain ⟨placeIndex, placeBelow, rfl, deeper⟩ := reaches_deeper children grows within back same
    have up := deeper index below rfl
    have down := grows component member placeIndex index placeBelow below isPlaced isChild
    omega

/-- **The location of a marker sitting at a marker's location does not reach back to where the outer one sits.** -/
theorem not_reaches_up_two {count : Nat} {components : List Pattern} {depth : Nat → Nat}
    (children : ∀ component ∈ components, ∀ child, childOf component = some child →
      ∃ index < count, child = .bvar index)
    (grows : ∀ component ∈ components, ∀ index child, index < count → child < count →
      placeAt component = some (.bvar index) → childOf component = some (.bvar child) → depth index < depth child)
    {list : List Pattern} (within : ∀ component ∈ list, component ∈ components) {upper lower place middle child : Pattern}
    (upperMember : upper ∈ components) (upperPlaced : placeAt upper = some place)
    (upperChild : childOf upper = some middle) (lowerMember : lower ∈ components)
    (lowerPlaced : placeAt lower = some middle) (lowerChild : childOf lower = some child) :
    ¬ Reaches list child place := by
  intro back
  obtain ⟨middleIndex, middleBelow, rfl⟩ := children upper upperMember middle upperChild
  obtain ⟨index, below, rfl⟩ := children lower lowerMember child lowerChild
  have lowerGrows := grows lower lowerMember middleIndex index middleBelow below lowerPlaced lowerChild
  by_cases same : Pattern.bvar index = place
  · subst same
    have := grows upper upperMember index middleIndex below middleBelow upperPlaced upperChild
    omega
  · obtain ⟨placeIndex, placeBelow, rfl, deeper⟩ := reaches_deeper children grows within back same
    have up := deeper index below rfl
    have upperGrows := grows upper upperMember placeIndex middleIndex placeBelow middleBelow upperPlaced upperChild
    omega

/-- **A component a filter keeps at most once is not among the others**, in any order of the list. -/
theorem not_mem_of_perm_unique {keep : Pattern → Bool} {list rest : List Pattern} {piece : Pattern}
    (atMostOne : (list.filter keep).length ≤ 1) (split : list.Perm (piece :: rest)) (kept : keep piece = true) :
    piece ∉ rest := by
  intro inRest
  have counted := (split.filter keep).length_eq
  rw [List.filter_cons_of_pos kept, List.length_cons] at counted
  have := List.length_pos_of_mem (List.mem_filter.mpr ⟨inRest, kept⟩)
  omega

/-! ## Where a move leaves its components -/

/-- **What a reaction leaves at a place its marker leaves**: the components there, the marker gone. -/
theorem reactList_filter_leaves {capability marker marker' : Pattern} {keep : Pattern → Bool}
    (capabilityApart : keep capability = false) (marker'Apart : keep marker' = false) (components : List Pattern) :
    (reactList capability marker marker' components).filter keep =
      (components.filter keep).filter fun component => component != marker := by
  unfold reactList
  have notIn : capability ∉ components.filter keep := fun inFiltered => by
    simp [capabilityApart] at inFiltered
  rw [List.filter_map]
  have filtered : (components.erase capability).filter
      (keep ∘ fun component => if component = marker then marker' else component) =
      (components.filter keep).filter fun component => component != marker := by
    rw [← List.erase_of_not_mem notIn, List.erase_filter, List.filter_filter]
    refine List.filter_congr fun component _ => ?_
    by_cases same : component = marker
    · subst same
      simp [marker'Apart]
    · simp [same]
  rw [filtered]
  conv_rhs => rw [← List.map_id ((components.filter keep).filter fun component => component != marker)]
  refine List.map_congr_left fun component member => ?_
  have different : component ≠ marker := by simpa using (List.mem_filter.mp member).2
  simp [different]

/-- Where the marker is not, a reaction only takes the capability away. -/
theorem reactList_of_not_mem {capability marker marker' : Pattern} {components : List Pattern}
    (noMarker : marker ∉ components) : reactList capability marker marker' components = components.erase capability := by
  unfold reactList
  conv_rhs => rw [← List.map_id (components.erase capability)]
  refine List.map_congr_left fun component member => ?_
  have different : component ≠ marker := fun same => noMarker (same ▸ List.mem_of_mem_erase member)
  simp [different]

/-- **What a reaction leaves at a place its marker arrives at**: the replacement beside the components there. -/
theorem reactList_filter_arrives {capability marker marker' : Pattern} {keep : Pattern → Bool}
    (capabilityApart : keep capability = false) (markerApart : keep marker = false) (marker'Kept : keep marker' = true)
    {components : List Pattern} (member : marker ∈ components) (once : marker ∉ components.erase marker)
    (different : capability ≠ marker) :
    ((reactList capability marker marker' components).filter keep).Perm (marker' :: components.filter keep) := by
  have split : components.Perm (marker :: components.erase marker) := List.perm_cons_erase member
  have reacted : (reactList capability marker marker' components).Perm
      (reactList capability marker marker' (marker :: components.erase marker)) := by
    unfold reactList
    exact (split.erase capability).map _
  have consIs : reactList capability marker marker' (marker :: components.erase marker) =
      marker' :: (components.erase marker).erase capability := by
    unfold reactList
    rw [List.erase_cons_tail (by simpa using different.symm), List.map_cons, if_pos rfl]
    congr 1
    conv_rhs => rw [← List.map_id ((components.erase marker).erase capability)]
    refine List.map_congr_left fun component inRest => ?_
    have differentMarker : component ≠ marker := by
      rintro rfl
      exact once (List.mem_of_mem_erase inRest)
    simp [differentMarker]
  refine (reacted.filter keep).trans ?_
  rw [consIs, List.filter_cons_of_pos marker'Kept]
  refine List.Perm.cons _ (.of_eq ?_)
  rw [← List.erase_filter, List.erase_of_not_mem (fun inFiltered => by simp [capabilityApart] at inFiltered),
    ← List.erase_filter, List.erase_of_not_mem (fun inFiltered => by simp [markerApart] at inFiltered)]

/-! ## The continuation's components beside the lifted ones -/

/-- **The continuation sits at no lifted place other than its home.** -/
theorem group_apart {owned : Nat} {home place : Pattern} {group : List Pattern}
    (groupPlaced : ∀ component ∈ group, ∀ at', placeAt component = some at' →
      at' = liftBVars 0 owned home ∨ ∃ index < owned, at' = .bvar index)
    (different : place ≠ home) : ∀ component ∈ group, placedAt (liftBVars 0 owned place) component = false := by
  intro component inGroup
  cases sits : placeAt component with
  | none => simp [placedAt, sits]
  | some at' =>
      have apart : at' ≠ liftBVars 0 owned place := by
        rcases groupPlaced component inGroup at' sits with atHome | ⟨index, belowOwned, isOwned⟩
        · rw [atHome]
          exact fun same => different (liftBVars_injective owned same).symm
        · rw [isOwned]
          exact fun same => lift_ne_owned belowOwned same.symm
      simp [placedAt, sits, apart]

theorem group_filter_apart {owned : Nat} {home place : Pattern} {group : List Pattern}
    (groupPlaced : ∀ component ∈ group, ∀ at', placeAt component = some at' →
      at' = liftBVars 0 owned home ∨ ∃ index < owned, at' = .bvar index)
    (different : place ≠ home) : group.filter (placedAt (liftBVars 0 owned place)) = [] :=
  List.filter_eq_nil_iff.mpr fun component inGroup isPlaced => by
    simp [group_apart groupPlaced different component inGroup] at isPlaced

theorem group_filter_beside {owned : Nat} {home place : Pattern} {group : List Pattern}
    (groupPlaced : ∀ component ∈ group, ∀ at', placeAt component = some at' →
      at' = liftBVars 0 owned home ∨ ∃ index < owned, at' = .bvar index)
    (different : place ≠ home) :
    group.filter (fun other => !placedAt (liftBVars 0 owned place) other) = group :=
  List.filter_eq_self.mpr fun component inGroup => by simp [group_apart groupPlaced different component inGroup]

/-- **Lifted components sit at none of the continuation's own locations.** -/
theorem lifted_apart (owned : Nat) (components : List Pattern) :
    ∀ component ∈ components.map (liftBVars 0 owned), ∀ at', placeAt component = some at' →
      ∀ index < owned, at' ≠ .bvar index := by
  intro component inLifted at' sits index below same
  obtain ⟨original, -, rfl⟩ := List.mem_map.mp inLifted
  rw [Mettapedia.GSLT.LanguageDef.RestrictionBlocks.liftBVars_eq_rename,
    Mettapedia.Languages.ProcessCalculi.Ambient.Decoding.placeAt_rename] at sits
  cases found : placeAt original with
  | none => rw [found] at sits; cases sits
  | some originalAt =>
      rw [found, Option.map_some, Option.some.injEq,
        ← Mettapedia.GSLT.LanguageDef.RestrictionBlocks.liftBVars_eq_rename] at sits
      rw [← sits] at same
      exact lift_ne_owned below same


/-- **The location of a marker sitting two markers below a place does not reach back to it.** -/
theorem not_reaches_up_three {count : Nat} {components : List Pattern} {depth : Nat → Nat}
    (children : ∀ component ∈ components, ∀ child, childOf component = some child →
      ∃ index < count, child = .bvar index)
    (grows : ∀ component ∈ components, ∀ index child, index < count → child < count →
      placeAt component = some (.bvar index) → childOf component = some (.bvar child) → depth index < depth child)
    {list : List Pattern} (within : ∀ component ∈ list, component ∈ components)
    {top upper lower place first second child : Pattern}
    (topMember : top ∈ components) (topPlaced : placeAt top = some place) (topChild : childOf top = some first)
    (upperMember : upper ∈ components) (upperPlaced : placeAt upper = some first)
    (upperChild : childOf upper = some second) (lowerMember : lower ∈ components)
    (lowerPlaced : placeAt lower = some second) (lowerChild : childOf lower = some child) :
    ¬ Reaches list child place := by
  intro back
  obtain ⟨firstIndex, firstBelow, rfl⟩ := children top topMember first topChild
  obtain ⟨secondIndex, secondBelow, rfl⟩ := children upper upperMember second upperChild
  obtain ⟨index, below, rfl⟩ := children lower lowerMember child lowerChild
  have upperGrows := grows upper upperMember firstIndex secondIndex firstBelow secondBelow upperPlaced upperChild
  have lowerGrows := grows lower lowerMember secondIndex index secondBelow below lowerPlaced lowerChild
  by_cases same : Pattern.bvar index = place
  · subst same
    have := grows top topMember index firstIndex below firstBelow topPlaced topChild
    omega
  · obtain ⟨placeIndex, placeBelow, rfl, deeper⟩ := reaches_deeper children grows within back same
    have up := deeper index below rfl
    have topGrows := grows top topMember placeIndex firstIndex placeBelow firstBelow topPlaced topChild
    omega

/-- **A place reached below another is reached through the marker placing an ambient at it**, whose own place is
reached too. -/
theorem Reaches.penultimate {components : List Pattern} {place target : Pattern}
    (reached : Reaches components place target) (different : place ≠ target) :
    ∃ marker ∈ components, childOf marker = some target ∧
      ∃ at', placeAt marker = some at' ∧ Reaches components place at' := by
  induction reached with
  | here => exact absurd rfl different
  | @down components place child target marker member isPlaced isChild below recurse =>
      by_cases same : child = target
      · subst same
        exact ⟨marker, member, isChild, place, by simpa [placedAt] using isPlaced, .here⟩
      · obtain ⟨last, inFiltered, lastChild, at', lastPlaced, reachedAt⟩ := recurse same
        exact ⟨last, (List.mem_filter.mp inFiltered).1, lastChild, at', lastPlaced,
          .down member isPlaced isChild reachedAt⟩

/-- **A bag inside a bag of ambient processes is flattened.** -/
theorem bag_flatten_ambient {bound : List TypeExpr} {pre inner post : List Pattern}
    (members : Members ambientCoreCalc ambientBlock free bound (pre ++ inner ++ post)) :
    ProcEquiv ambientCoreCalc ambientBlock free bound
      (.collection .hashBag (pre ++ .collection .hashBag inner none :: post) none)
      (.collection .hashBag (pre ++ inner ++ post) none) := by
  have signature := Mettapedia.Languages.ProcessCalculi.Ambient.Comm.coreSignature
  have innerTyped : HasType ambientCoreCalc free bound (.collection .hashBag inner none) procType :=
    signature.bag_typed (rest := none) (elementsHaveType_iff.mpr fun element member =>
      members element (by simp [member]))
  have sourceTyped : HasType ambientCoreCalc free bound
      (.collection .hashBag (pre ++ .collection .hashBag inner none :: post) none) procType :=
    signature.bag_typed (rest := none) (elementsHaveType_iff.mpr fun element member => by
      simp only [List.mem_append, List.mem_cons] at member
      rcases member with inPre | rfl | inPost
      · exact members element (by simp [inPre])
      · exact innerTyped
      · exact members element (by simp [inPost]))
  have targetTyped : HasType ambientCoreCalc free bound (.collection .hashBag (pre ++ inner ++ post) none) procType :=
    signature.bag_typed (rest := none) (elementsHaveType_iff.mpr members)
  exact Mettapedia.GSLT.LanguageDef.RestrictionBlocks.SortedEquiv.ofDerived (signature.flatten sourceTyped)
    sourceTyped targetTyped


/-! ## Entering at its place -/

/-- **An entry at its place reads as an entry there**: the moving ambient, the capability in it and the ambient it
enters, read at the place both sit at, step to the target ambient holding the moved one, which is what the reacted
components read as there, under the continuation's restrictions. -/
theorem enter_local {bound : List TypeExpr} {count : Nat} {components : List Pattern} {depth : Nat → Nat}
    (children : ∀ component ∈ components, ∀ child, childOf component = some child →
      ∃ index < count, child = .bvar index)
    (grows : ∀ component ∈ components, ∀ index child, index < count → child < count →
      placeAt component = some (.bvar index) → childOf component = some (.bvar child) → depth index < depth child)
    (unique : ∀ child, (components.filter fun component => childOf component == some child).length ≤ 1)
    (typed : Members locatedCalc locatedBlock free bound components)
    {parent mover target moverName targetName continuation : Pattern} {owned : Nat} {group : List Pattern}
    (moverNameVar : isVariable moverName = true) (targetNameVar : isVariable targetName = true)
    (decomposed : decompose locatedBlock continuation = ⟨owned, group⟩)
    (groupPlaced : ∀ component ∈ group, ∀ at', placeAt component = some at' →
      at' = liftBVars 0 owned mover ∨ ∃ index < owned, at' = .bvar index)
    (groupChildren : ∀ component ∈ group, ∀ child, childOf component = some child →
      ∃ index < owned, child = .bvar index)
    (groupTyped : Members locatedCalc locatedBlock free (List.replicate owned nameType ++ bound) group)
    {list : List Pattern} (sub : list.Sublist components)
    (markerIn : Pattern.apply "LAmb" [parent, mover, moverName] ∈ list)
    (capabilityIn : Pattern.apply "LIn" [mover, targetName, continuation] ∈ list)
    (destinationIn : Pattern.apply "LAmb" [parent, target, targetName] ∈ list)
    (apartTargets : mover ≠ target)
    (fuel : Nat) (enough : 3 * sizeList list + 6 ≤ fuel) :
    ∃ result, AmbNuRawStep (.collection .hashBag ((readPlaced fuel parent list).map padA) none) result ∧
      ProcEquiv ambientCoreCalc ambientBlock free bound result (Prenex.restricts ambientBlock owned
        (Prenex.body ambientBlock (readPlaced fuel (liftBVars 0 owned parent)
          ((reactList (.apply "LIn" [mover, targetName, continuation]) (.apply "LAmb" [parent, mover, moverName])
            (.apply "LAmb" [target, mover, moverName]) list).map (liftBVars 0 owned) ++ group)))) := by
  have within : ∀ component ∈ list, component ∈ components := fun component inList => sub.subset inList
  obtain ⟨g, rfl⟩ : ∃ g, fuel = g + 6 := ⟨fuel - 6, by omega⟩
  set capability := Pattern.apply "LIn" [mover, targetName, continuation] with capabilityIs
  set marker := Pattern.apply "LAmb" [parent, mover, moverName] with markerIs
  set marker' := Pattern.apply "LAmb" [target, mover, moverName] with marker'Is
  set destination := Pattern.apply "LAmb" [parent, target, targetName] with destinationIs
  have inListed : "LIn" ∈ capabilities := by simp [capabilities]
  have ambMarker : "LAmb" ∈ markers := by simp [markers]
  have capabilityAt : placeAt capability = some mover := placeAt_capability inListed _ _ _
  have markerAt : placeAt marker = some parent := placeAt_ofMarker ambMarker _ _ _
  have marker'At : placeAt marker' = some target := placeAt_ofMarker ambMarker _ _ _
  have destinationAt : placeAt destination = some parent := placeAt_ofMarker ambMarker _ _ _
  have markerChild : childOf marker = some mover := by simp [markerIs, childOf, markers]
  have destinationChild : childOf destination = some target := by simp [destinationIs, childOf, markers]
  have moverParent : mover ≠ parent :=
    child_ne_place children grows (within _ markerIn) (by simp [placedAt, markerAt]) markerChild
  have targetParent : target ≠ parent :=
    child_ne_place children grows (within _ destinationIn) (by simp [placedAt, destinationAt]) destinationChild
  have uniqueList : ∀ child, (list.filter fun component => childOf component == some child).length ≤ 1 :=
    fun child => le_trans (sub.filter _).length_le (unique child)
  have onlyMarker : ∀ component ∈ list, childOf component = some mover → component = marker :=
    fun component member isChild => eq_of_filter_length_le_one (uniqueList mover) member markerIn
      (by simp [isChild]) (by simp [markerChild])
  have onlyDestination : ∀ component ∈ list, childOf component = some target → component = destination :=
    fun component member isChild => eq_of_filter_length_le_one (uniqueList target) member destinationIn
      (by simp [isChild]) (by simp [destinationChild])
  -- the ambients at the place, the moving one and the target among them
  set here := list.filter (placedAt parent) with hereIs
  set elsewhere := list.filter fun other => !placedAt parent other with elsewhereIs
  have markerHere : marker ∈ here := List.mem_filter.mpr ⟨markerIn, by simp [placedAt, markerAt]⟩
  have destinationHere : destination ∈ here := List.mem_filter.mpr ⟨destinationIn, by simp [placedAt, destinationAt]⟩
  have capabilityElsewhere : capability ∈ elsewhere :=
    List.mem_filter.mpr ⟨capabilityIn, by simp [placedAt, capabilityAt, moverParent]⟩
  have markerNotElsewhere : marker ∉ elsewhere := fun inElsewhere => by
    simp [elsewhereIs, placedAt, markerAt] at inElsewhere
  have destinationNotElsewhere : destination ∉ elsewhere := fun inElsewhere => by
    simp [elsewhereIs, placedAt, destinationAt] at inElsewhere
  have markerDestination : marker ≠ destination := fun same => apartTargets (by
    have children' := congrArg childOf same
    rw [markerChild, destinationChild] at children'
    exact Option.some.inj children')
  obtain ⟨i, hi, markerAtI⟩ := List.getElem_of_mem markerHere
  have destinationRest : destination ∈ here.eraseIdx i := by
    obtain ⟨j₀, hj₀, at₀⟩ := List.getElem_of_mem destinationHere
    refine List.mem_eraseIdx_iff_getElem.mpr ⟨j₀, hj₀, fun same => ?_, at₀⟩
    subst same
    exact markerDestination (markerAtI.symm.trans at₀)
  obtain ⟨j, hj, destinationAtJ⟩ := List.getElem_of_mem destinationRest
  set others := (here.eraseIdx i).eraseIdx j with othersIs
  have hereSplit : here.Perm (marker :: destination :: others) := by
    have split := perm_two here i hi j hj
    rwa [markerAtI, destinationAtJ] at split
  have hereSub : here.Sublist components := List.filter_sublist.trans sub
  have uniqueHere : ∀ child, (here.filter fun component => childOf component == some child).length ≤ 1 :=
    fun child => le_trans (hereSub.filter _).length_le (unique child)
  have markerOnce : marker ∉ destination :: others :=
    not_mem_of_perm_unique (uniqueHere mover) hereSplit (by simp [markerChild])
  have destinationOnce : destination ∉ marker :: others :=
    not_mem_of_perm_unique (uniqueHere target) (hereSplit.trans (.swap _ _ _)) (by simp [destinationChild])
  have markerNotOthers : marker ∉ others := fun inOthers => markerOnce (List.mem_cons_of_mem _ inOthers)
  have destinationNotOthers : destination ∉ others := fun inOthers => destinationOnce (List.mem_cons_of_mem _ inOthers)
  have othersHere : ∀ component ∈ others, component ∈ here := fun component inOthers =>
    hereSplit.symm.subset (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ inOthers))
  -- what sits in the two ambients
  set atMover := elsewhere.filter (placedAt mover) with atMoverIs
  set besideMover := elsewhere.filter fun other => !placedAt mover other with besideMoverIs
  set atTarget := elsewhere.filter (placedAt target) with atTargetIs
  set besideTarget := elsewhere.filter fun other => !placedAt target other with besideTargetIs
  have capabilityAtMover : capability ∈ atMover :=
    List.mem_filter.mpr ⟨capabilityElsewhere, by simp [placedAt, capabilityAt]⟩
  obtain ⟨k, hk, capabilityAtK⟩ := List.getElem_of_mem capabilityAtMover
  -- the source: the entry on the padded items at the place
  set readS := fun component => readComponent (g + 5) parent component elsewhere with readSIs
  have sourceIs : (readPlaced (g + 6) parent list).map padA = here.map (padA ∘ readS) := by
    rw [readPlaced_succ, List.map_map]
  have elsewhereSize : sizeList elsewhere + 4 ≤ sizeList list := by
    have split : size marker + sizeList elsewhere ≤ sizeList list := size_add_elsewhere markerHere
    have markerSize : 4 ≤ size marker := by
      simp only [markerIs, size, sizeList]
      have := size_pos parent
      have := size_pos mover
      have := size_pos moverName
      omega
    omega
  have settledMover : readPlaced (g + 4) mover elsewhere = readPlaced (g + 2) mover elsewhere :=
    readPlaced_settled mover elsewhere (by omega) (by omega)
  set readM := fun component => readComponent (g + 1) mover component besideMover with readMIs
  have moverContent : readPlaced (g + 2) mover elsewhere = atMover.map readM := by
    rw [readPlaced_succ]
  have moverRead : (padA ∘ readS) marker =
      .apply "AAmb" [moverName, .collection .hashBag ((atMover.map readM).map padA) none] := by
    simp only [Function.comp, readSIs]
    rw [padded_amb (g + 3) parent moverNameVar capabilityElsewhere (by simp [placedAt, capabilityAt])
      (fun _ _ _ => by simp [capabilityIs]), settledMover, moverContent]
  set continuationRead := Prenex.toPattern ambientBlock (decodeForm g mover (decompose locatedBlock continuation))
    with continuationReadIs
  have capabilityRead : padA (readM capability) = .apply "AIn" [targetName, padA continuationRead] := by
    simp only [readMIs, capabilityIs]
    rw [readComponent_capability g mover inListed targetNameVar, show ambientCapability "LIn" = "AIn" by decide,
      padA_capability (by decide) targetNameVar]
  have hkInner : k < ((atMover.map readM).map padA).length := by simpa using hk
  have capabilityItem : ((atMover.map readM).map padA)[k] = .apply "AIn" [targetName, padA continuationRead] := by
    rw [List.getElem_map, List.getElem_map, capabilityAtK, capabilityRead]
  set targetContent := Prenex.body ambientBlock (readPlaced (g + 4) target elsewhere) with targetContentIs
  have destinationRead : (padA ∘ readS) destination = .apply "AAmb" [targetName, asBag (padA targetContent)] := by
    simp only [Function.comp, readSIs, destinationIs]
    rw [readComponent_amb (g + 4) parent targetNameVar, padA_amb targetNameVar]
  have hiItems : i < (here.map (padA ∘ readS)).length := by simpa using hi
  have moverItem : (here.map (padA ∘ readS))[i] =
      amb moverName (.collection .hashBag ((atMover.map readM).map padA) none) := by
    rw [List.getElem_map, markerAtI, moverRead]
    rfl
  have erasedMap : (here.map (padA ∘ readS)).eraseIdx i = (here.eraseIdx i).map (padA ∘ readS) :=
    List.eraseIdx_map _ _ _
  have hjItems : j < ((here.map (padA ∘ readS)).eraseIdx i).length := by rw [erasedMap]; simpa using hj
  have destinationItem : ((here.map (padA ∘ readS)).eraseIdx i)[j] =
      amb targetName (asBag (padA targetContent)) := by
    refine (List.getElem_of_eq erasedMap hjItems).trans ?_
    rw [List.getElem_map, destinationAtJ, destinationRead]
    rfl
  have step := AmbNuRawStep.enter (tail := none) i hiItems j hjItems moverName targetName (padA continuationRead)
    (asBag (padA targetContent)) k hkInner moverItem capabilityItem destinationItem
  have restIs : ((here.map (padA ∘ readS)).eraseIdx i).eraseIdx j = others.map (padA ∘ readS) := by
    rw [erasedMap, List.eraseIdx_map]
  rw [restIs] at step
  rw [sourceIs]
  refine ⟨_, step, ?_⟩
  -- the reacted components, place by place
  set reacted := reactList capability marker marker' list with reactedIs
  have capabilityMarker : capability ≠ marker := by simp [capabilityIs, markerIs]
  have markerOnceList : marker ∉ list.erase marker :=
    not_mem_of_perm_unique (uniqueList mover) (List.perm_cons_erase markerIn) (by simp [markerChild])
  have reactedHere : reacted.filter (placedAt parent) = here.filter fun component => component != marker :=
    reactList_filter_leaves (by simp [placedAt, capabilityAt, moverParent])
      (by simp [placedAt, marker'At, targetParent]) list
  have reactedAtTarget : (reacted.filter (placedAt target)).Perm (marker' :: atTarget) := by
    have arrives := reactList_filter_arrives (keep := placedAt target) (marker' := marker')
      (by simp [placedAt, capabilityAt, apartTargets]) (by simp [placedAt, markerAt, Ne.symm targetParent])
      (by simp [placedAt, marker'At]) markerIn markerOnceList capabilityMarker
    rwa [show list.filter (placedAt target) = atTarget from (filter_at_elsewhere targetParent list).symm] at arrives
  have reactedAtMover : reacted.filter (placedAt mover) = atMover.erase capability := by
    rw [reactedIs, reactList_filter (show placedAt mover marker' = placedAt mover marker by
      simp [placedAt, marker'At, markerAt, Ne.symm apartTargets, Ne.symm moverParent])]
    rw [reactList_of_not_mem (fun inFiltered => by simp [placedAt, markerAt, Ne.symm moverParent] at inFiltered),
      atMoverIs, filter_at_elsewhere moverParent]
  have reactedAway : ∀ {at' : Pattern}, at' ≠ parent → at' ≠ mover → at' ≠ target →
      reacted.filter (placedAt at') = list.filter (placedAt at') := fun awayParent awayMover awayTarget =>
    reactList_at (by simp [placedAt, capabilityAt, Ne.symm awayMover])
      (by simp [placedAt, markerAt, Ne.symm awayParent]) (by simp [placedAt, marker'At, Ne.symm awayTarget])
  -- the target's lists, level by level
  set elsewhere' := (reacted.filter fun other => !placedAt parent other).map (liftBVars 0 owned) ++ group
    with elsewhere'Is
  set elsewhere'' := elsewhere'.filter fun other => !placedAt (liftBVars 0 owned target) other with elsewhere''Is
  set elsewhere''' := elsewhere''.filter fun other => !placedAt (liftBVars 0 owned mover) other
    with elsewhere'''Is
  set groupHere := group.filter (placedAt (liftBVars 0 owned mover)) with groupHereIs
  set groupDeep := group.filter fun other => !placedAt (liftBVars 0 owned mover) other with groupDeepIs
  have liftApart : ∀ {first second : Pattern}, first ≠ second →
      liftBVars 0 owned first ≠ liftBVars 0 owned second := fun different same =>
    different (liftBVars_injective owned same)
  set readT := fun component => readComponent (g + 5) (liftBVars 0 owned parent) component elsewhere' with readTIs
  have hereT : (reacted.map (liftBVars 0 owned) ++ group).filter (placedAt (liftBVars 0 owned parent)) =
      (here.filter fun component => component != marker).map (liftBVars 0 owned) := by
    rw [List.filter_append, filter_lift_at, reactedHere, group_filter_apart groupPlaced (Ne.symm moverParent),
      List.append_nil]
  have elsewhereT : (reacted.map (liftBVars 0 owned) ++ group).filter
      (fun other => !placedAt (liftBVars 0 owned parent) other) = elsewhere' := by
    rw [List.filter_append, filter_lift_elsewhere, group_filter_beside groupPlaced (Ne.symm moverParent)]
  have targetIs : readPlaced (g + 6) (liftBVars 0 owned parent) (reacted.map (liftBVars 0 owned) ++ group) =
      ((here.filter fun component => component != marker).map (liftBVars 0 owned)).map readT := by
    rw [readPlaced_succ, hereT, elsewhereT]
  rw [targetIs]
  set readTT := fun component => readComponent (g + 3) (liftBVars 0 owned target) component elsewhere''
    with readTTIs
  have atTargetT : elsewhere'.filter (placedAt (liftBVars 0 owned target)) =
      (reacted.filter (placedAt target)).map (liftBVars 0 owned) := by
    rw [elsewhere'Is, List.filter_append, filter_lift_at, filter_at_elsewhere targetParent,
      group_filter_apart groupPlaced (Ne.symm apartTargets), List.append_nil]
  have liftedDestination : liftBVars 0 owned destination = .apply "LAmb"
      [liftBVars 0 owned parent, liftBVars 0 owned target, liftBVars 0 owned targetName] := by
    simp [destinationIs, liftBVars, Mettapedia.OSLF.MeTTaIL.Substitution.liftBVarsList_eq_map]
  have destinationReadT : readT (liftBVars 0 owned destination) = .apply "AAmb" [liftBVars 0 owned targetName,
      Prenex.body ambientBlock (((reacted.filter (placedAt target)).map (liftBVars 0 owned)).map readTT)] := by
    simp only [readTIs]
    rw [liftedDestination, readComponent_amb (g + 4) _ (by rw [isVariable_lift]; exact targetNameVar),
      readPlaced_succ, atTargetT]
  set readMM := fun component => readComponent (g + 1) (liftBVars 0 owned mover) component elsewhere'''
    with readMMIs
  have atMoverT : elsewhere''.filter (placedAt (liftBVars 0 owned mover)) =
      (atMover.erase capability).map (liftBVars 0 owned) ++ groupHere := by
    rw [elsewhere''Is, filter_at_elsewhere (liftApart apartTargets), elsewhere'Is, List.filter_append, filter_lift_at,
      filter_at_elsewhere moverParent, reactedAtMover]
  have liftedMarker' : liftBVars 0 owned marker' = .apply "LAmb"
      [liftBVars 0 owned target, liftBVars 0 owned mover, liftBVars 0 owned moverName] := by
    simp [marker'Is, liftBVars, Mettapedia.OSLF.MeTTaIL.Substitution.liftBVarsList_eq_map]
  have marker'ReadT : readTT (liftBVars 0 owned marker') = .apply "AAmb" [liftBVars 0 owned moverName,
      Prenex.body ambientBlock (((atMover.erase capability).map (liftBVars 0 owned) ++ groupHere).map readMM)] := by
    simp only [readTTIs]
    rw [liftedMarker', readComponent_amb (g + 2) _ (by rw [isVariable_lift]; exact moverNameVar), readPlaced_succ,
      atMoverT]
  have deepestIs : elsewhere''' = (((reacted.filter fun other => !placedAt parent other).filter
      fun other => !placedAt target other).filter fun other => !placedAt mover other).map (liftBVars 0 owned) ++
        groupDeep := by
    rw [elsewhere'''Is, elsewhere''Is, elsewhere'Is, List.filter_append, List.filter_append, filter_lift_elsewhere,
      filter_lift_elsewhere, group_filter_beside groupPlaced (Ne.symm apartTargets)]
  -- the continuation, read at the mover's location
  have groupDeepChildren : ∀ component ∈ groupDeep, ∀ child, childOf component = some child →
      ∃ index < owned, child = .bvar index := fun component inDeep =>
    groupChildren component (List.mem_filter.mp inDeep).1
  have groupRead : ∀ component ∈ groupHere,
      readMM component = readComponent (g + 1) (liftBVars 0 owned mover) component groupDeep := by
    intro component inHere'
    simp only [readMMIs]
    rw [deepestIs]
    exact group_reads groupDeepChildren (lifted_apart owned _) (g + 1) _ component
      (groupChildren component (List.mem_filter.mp inHere').1)
  have massBound : 3 * Prenex.mass ⟨owned, group⟩ + 3 ≤ g := by
    have massLe := Mettapedia.GSLT.LanguageDef.RestrictionBlocks.mass_decompose (block := locatedBlock) continuation
    rw [decomposed] at massLe
    have capabilitySize : size continuation + 3 ≤ size capability := by
      simp only [capabilityIs, size, sizeList]
      have := size_pos mover
      have := size_pos targetName
      omega
    have listSize := size_le_sizeList capabilityElsewhere
    omega
  have continuationIs : continuationRead = Prenex.restricts ambientBlock owned (Prenex.body ambientBlock
      (groupHere.map fun component => readComponent (g + 1) (liftBVars 0 owned mover) component groupDeep)) := by
    rw [continuationReadIs, decomposed, decodeForm_settled mover _ massBound (show 3 * _ + 3 ≤ g + 3 by omega)]
    simp only [decodeForm, Prenex.toPattern]
    rw [readPlaced_succ]
  -- the untouched components read as before, lifted
  have elsewhereWithin : ∀ component ∈ elsewhere, component ∈ components := fun component inElsewhere =>
    within component (List.mem_filter.mp inElsewhere).1
  have besideMoverWithin : ∀ component ∈ besideMover, component ∈ components := fun component inBeside =>
    elsewhereWithin component (List.mem_filter.mp inBeside).1
  have besideTargetWithin : ∀ component ∈ besideTarget, component ∈ components := fun component inBeside =>
    elsewhereWithin component (List.mem_filter.mp inBeside).1
  have noMoverChild : ∀ component ∈ elsewhere, childOf component ≠ some mover := fun component inElsewhere isChild =>
    markerNotElsewhere (onlyMarker component (List.mem_filter.mp inElsewhere).1 isChild ▸ inElsewhere)
  have noTargetChild : ∀ component ∈ elsewhere, childOf component ≠ some target :=
    fun component inElsewhere isChild =>
      destinationNotElsewhere (onlyDestination component (List.mem_filter.mp inElsewhere).1 isChild ▸ inElsewhere)
  have changedAt : ∀ {at' : Pattern}, at' ≠ parent → at' ≠ mover → at' ≠ target →
      elsewhere'.filter (placedAt (liftBVars 0 owned at')) = (list.filter (placedAt at')).map (liftBVars 0 owned) := by
    intro at' awayParent awayMover awayTarget
    rw [elsewhere'Is, List.filter_append, filter_lift_at, filter_at_elsewhere awayParent,
      reactedAway awayParent awayMover awayTarget, group_filter_apart groupPlaced awayMover, List.append_nil]
  have changedAt'' : ∀ {at' : Pattern}, at' ≠ parent → at' ≠ mover → at' ≠ target →
      elsewhere''.filter (placedAt (liftBVars 0 owned at')) = (list.filter (placedAt at')).map (liftBVars 0 owned) := by
    intro at' awayParent awayMover awayTarget
    rw [elsewhere''Is, filter_at_elsewhere (liftApart awayTarget), changedAt awayParent awayMover awayTarget]
  have changedAt''' : ∀ {at' : Pattern}, at' ≠ parent → at' ≠ mover → at' ≠ target →
      elsewhere'''.filter (placedAt (liftBVars 0 owned at')) =
        (list.filter (placedAt at')).map (liftBVars 0 owned) := by
    intro at' awayParent awayMover awayTarget
    rw [elsewhere'''Is, filter_at_elsewhere (liftApart awayMover), changedAt'' awayParent awayMover awayTarget]
  have othersRead : ∀ component ∈ others,
      readT (liftBVars 0 owned component) = liftBVars 0 owned (readS component) := by
    intro component inOthers
    have inHere := othersHere component inOthers
    have member := (List.mem_filter.mp inHere).1
    have placed : placeAt component = some parent := by simpa [placedAt] using (List.mem_filter.mp inHere).2
    refine readComponent_lift_congr (g + 5) fun child isChild at' reached => ?_
    have awayParent : at' ≠ parent := fun same =>
      not_reaches_up children grows elsewhereWithin (within _ member) placed isChild (same ▸ reached)
    have awayMover : at' ≠ mover := fun same => by
      refine not_reaches_unmarked noMoverChild (fun same' => ?_) (same ▸ reached)
      subst same'
      exact markerNotOthers (onlyMarker component member isChild ▸ inOthers)
    have awayTarget : at' ≠ target := fun same => by
      refine not_reaches_unmarked noTargetChild (fun same' => ?_) (same ▸ reached)
      subst same'
      exact destinationNotOthers (onlyDestination component member isChild ▸ inOthers)
    rw [changedAt awayParent awayMover awayTarget, filter_at_elsewhere awayParent]
  have targetItemsRead : ∀ component ∈ atTarget, readTT (liftBVars 0 owned component) =
      liftBVars 0 owned (readComponent (g + 3) target component besideTarget) := by
    intro component inTarget
    have inElsewhere := (List.mem_filter.mp inTarget).1
    have member := (List.mem_filter.mp inElsewhere).1
    have placed : placeAt component = some target := by simpa [placedAt] using (List.mem_filter.mp inTarget).2
    refine readComponent_lift_congr (g + 3) fun child isChild at' reached => ?_
    have awayTarget : at' ≠ target := fun same =>
      not_reaches_up children grows besideTargetWithin (within _ member) placed isChild (same ▸ reached)
    have awayParent : at' ≠ parent := fun same =>
      not_reaches_up_two children grows besideTargetWithin (within _ destinationIn) destinationAt destinationChild
        (within _ member) placed isChild (same ▸ reached)
    have awayMover : at' ≠ mover := fun same => by
      refine not_reaches_unmarked (fun other inBeside => noMoverChild other (List.mem_filter.mp inBeside).1)
        (fun same' => ?_) (same ▸ reached)
      subst same'
      exact markerNotElsewhere (onlyMarker component member isChild ▸ inElsewhere)
    rw [changedAt'' awayParent awayMover awayTarget, besideTargetIs, filter_at_elsewhere awayTarget,
      filter_at_elsewhere awayParent]
  have moverItemsRead : ∀ component ∈ atMover,
      readMM (liftBVars 0 owned component) = liftBVars 0 owned (readM component) := by
    intro component inMover
    have inElsewhere := (List.mem_filter.mp inMover).1
    have member := (List.mem_filter.mp inElsewhere).1
    have placed : placeAt component = some mover := by simpa [placedAt] using (List.mem_filter.mp inMover).2
    refine readComponent_lift_congr (g + 1) fun child isChild at' reached => ?_
    have awayMover : at' ≠ mover := fun same =>
      not_reaches_up children grows besideMoverWithin (within _ member) placed isChild (same ▸ reached)
    have awayParent : at' ≠ parent := fun same =>
      not_reaches_up_two children grows besideMoverWithin (within _ markerIn) markerAt markerChild
        (within _ member) placed isChild (same ▸ reached)
    have awayTarget : at' ≠ target := fun same => by
      refine not_reaches_unmarked (fun other inBeside => noTargetChild other (List.mem_filter.mp inBeside).1)
        (fun same' => ?_) (same ▸ reached)
      subst same'
      exact destinationNotElsewhere (onlyDestination component member isChild ▸ inElsewhere)
    rw [changedAt''' awayParent awayMover awayTarget, besideMoverIs, filter_at_elsewhere awayMover,
      filter_at_elsewhere awayParent]
  -- typing
  have listMembers : Members locatedCalc locatedBlock free bound list := fun component inList =>
    typed component (within component inList)
  have elsewhereMembers : Members locatedCalc locatedBlock free bound elsewhere := fun component inElsewhere =>
    listMembers component (List.mem_filter.mp inElsewhere).1
  have nameTypes : ∀ {place child name : Pattern}, Pattern.apply "LAmb" [place, child, name] ∈ list →
      HasType locatedCalc free bound child nameType ∧ HasType locatedCalc free bound name nameType := by
    intro place child name member
    rcases triple_inv (listMembers _ member) with ⟨-, second, third⟩ | ⟨listed, -, -⟩ | ⟨isCap, -, -⟩
    · exact ⟨second, third⟩
    · simp [capabilities] at listed
    · simp at isCap
  obtain ⟨moverTyped, moverNameTyped⟩ := nameTypes markerIn
  obtain ⟨targetTyped, targetNameTyped⟩ := nameTypes destinationIn
  have marker'Typed : HasType locatedCalc free bound marker' procType :=
    Mettapedia.Languages.ProcessCalculi.Ambient.Encoding.marker_typed targetTyped moverTyped moverNameTyped
  have moverNameTyped' : HasType ambientCoreCalc free bound moverName nameType :=
    variable_typed moverNameTyped moverNameVar
  have targetNameTyped' : HasType ambientCoreCalc free bound targetName nameType :=
    variable_typed targetNameTyped targetNameVar
  have reactedMembers : Members locatedCalc locatedBlock free bound reacted := by
    intro component inReacted
    rcases mem_reactList inReacted with inList | rfl
    · exact listMembers component inList
    · exact marker'Typed
  have extended : Members locatedCalc locatedBlock free (List.replicate owned nameType ++ bound)
      (reacted.map (liftBVars 0 owned) ++ group) := by
    have lifted := Mettapedia.GSLT.LanguageDef.RestrictionBlocks.Members.lift (language := locatedCalc)
      (block := locatedBlock) (List.replicate owned nameType) reactedMembers
    rw [List.length_replicate] at lifted
    exact lifted.append groupTyped
  have elsewhere'Members : Members locatedCalc locatedBlock free (List.replicate owned nameType ++ bound)
      elsewhere' := fun component inElsewhere' => extended component (by
        rw [← elsewhereT] at inElsewhere'
        exact (List.mem_filter.mp inElsewhere').1)
  have elsewhere''Members : Members locatedCalc locatedBlock free (List.replicate owned nameType ++ bound)
      elsewhere'' := fun component inElsewhere'' => elsewhere'Members component (List.mem_filter.mp inElsewhere'').1
  -- the source's pieces, typed
  have hereReadMembers : Members ambientCoreCalc ambientBlock free bound (here.map readS) := by
    have reading := (decode_typed (g + 6)).2.1 parent list listMembers
    rwa [readPlaced_succ] at reading
  have hereReadObjects : ∀ item ∈ here.map readS, isObjectPattern item = true := by
    have objects := (decode_object (g + 6)).2.1 parent list
    rwa [readPlaced_succ] at objects
  have othersMembers : Members ambientCoreCalc ambientBlock free bound (others.map readS) := fun item inItems => by
    obtain ⟨original, inOthers, rfl⟩ := List.mem_map.mp inItems
    exact hereReadMembers _ (List.mem_map_of_mem (othersHere original inOthers))
  have othersObjects : ∀ item ∈ others.map readS, isObjectPattern item = true := fun item inItems => by
    obtain ⟨original, inOthers, rfl⟩ := List.mem_map.mp inItems
    exact hereReadObjects _ (List.mem_map_of_mem (othersHere original inOthers))
  have moverMembers : Members ambientCoreCalc ambientBlock free bound (atMover.map readM) := by
    have reading := (decode_typed (g + 2)).2.1 mover elsewhere elsewhereMembers
    rwa [moverContent] at reading
  have moverObjects : ∀ item ∈ atMover.map readM, isObjectPattern item = true := by
    have objects := (decode_object (g + 2)).2.1 mover elsewhere
    rwa [moverContent] at objects
  set targetKept := atTarget.map fun component => readComponent (g + 3) target component besideTarget
    with targetKeptIs
  have targetReadIs : readPlaced (g + 4) target elsewhere = targetKept := by
    rw [readPlaced_succ]
  have targetContentIs' : targetContent = Prenex.body ambientBlock targetKept := by
    rw [targetContentIs, targetReadIs]
  have targetMembers : Members ambientCoreCalc ambientBlock free bound targetKept := by
    have reading := (decode_typed (g + 4)).2.1 target elsewhere elsewhereMembers
    rwa [targetReadIs] at reading
  have targetObjects : ∀ item ∈ targetKept, isObjectPattern item = true := by
    have objects := (decode_object (g + 4)).2.1 target elsewhere
    rwa [targetReadIs] at objects
  have continuationTyped : HasType ambientCoreCalc free bound continuationRead procType := by
    rw [continuationReadIs, decomposed]
    exact decodeForm_typed g mover groupTyped
  have continuationObject : isObjectPattern continuationRead = true :=
    Mettapedia.GSLT.LanguageDef.RestrictionBlocks.isObject_toPattern ((decode_object g).1 mover _)
  set moverKept := (atMover.erase capability).map readM with moverKeptIs
  have moverKeptMembers : Members ambientCoreCalc ambientBlock free bound moverKept := fun item inItems => by
    obtain ⟨original, inErased, rfl⟩ := List.mem_map.mp inItems
    exact moverMembers _ (List.mem_map_of_mem (List.mem_of_mem_erase inErased))
  have groupReadMembers : Members ambientCoreCalc ambientBlock free (List.replicate owned nameType ++ bound)
      (groupHere.map fun component => readComponent (g + 1) (liftBVars 0 owned mover) component groupDeep) := by
    have reading := (decode_typed (g + 2)).2.1 (liftBVars 0 owned mover) group groupTyped
    rwa [readPlaced_succ] at reading
  -- the common form both sides are equivalent to
  set movedContent := Prenex.body ambientBlock (continuationRead :: moverKept) with movedContentIs
  set moved := Pattern.apply "AAmb" [moverName, movedContent] with movedIs
  set entered := Pattern.apply "AAmb" [targetName, Prenex.body ambientBlock (moved :: targetKept)] with enteredIs
  have movedContentTyped : HasType ambientCoreCalc free bound movedContent procType :=
    body_typed (Members.cons continuationTyped moverKeptMembers)
  have movedTyped : HasType ambientCoreCalc free bound moved procType := amb_typed moverNameTyped' movedContentTyped
  have enteredTyped : HasType ambientCoreCalc free bound entered procType :=
    amb_typed targetNameTyped' (body_typed (Members.cons movedTyped targetMembers))
  -- the target side: restrictions moved down into the moved ambient
  have moverItemsIs : ((atMover.erase capability).map (liftBVars 0 owned) ++ groupHere).map readMM =
      moverKept.map (liftBVars 0 owned) ++
        groupHere.map fun component => readComponent (g + 1) (liftBVars 0 owned mover) component groupDeep := by
    rw [List.map_append, List.map_map, moverKeptIs, List.map_map]
    refine congrArg₂ (· ++ ·) (List.map_congr_left fun component inErased => ?_)
      (List.map_congr_left fun component inGroup => groupRead component inGroup)
    exact moverItemsRead component (List.mem_of_mem_erase inErased)
  have moverBodyTyped : HasType ambientCoreCalc free (List.replicate owned nameType ++ bound)
      (Prenex.body ambientBlock (((atMover.erase capability).map (liftBVars 0 owned) ++ groupHere).map readMM))
      procType := by
    have reading := (decode_typed (g + 2)).2.1 (liftBVars 0 owned mover) elsewhere'' elsewhere''Members
    rw [readPlaced_succ, atMoverT] at reading
    exact body_typed reading
  have movedSide : ProcEquiv ambientCoreCalc ambientBlock free bound
      (Prenex.restricts ambientBlock owned (readTT (liftBVars 0 owned marker'))) moved := by
    rw [marker'ReadT]
    refine .trans _ _ _ (restricts_amb_equivalent owned moverNameTyped' moverBodyTyped) (amb_fill moverNameTyped' ?_)
    rw [moverItemsIs, movedContentIs, continuationIs]
    exact restricts_body_split owned moverKeptMembers groupReadMembers
  have targetItemsPerm : (((reacted.filter (placedAt target)).map (liftBVars 0 owned)).map readTT).Perm
      (readTT (liftBVars 0 owned marker') :: targetKept.map (liftBVars 0 owned)) := by
    refine ((reactedAtTarget.map (liftBVars 0 owned)).map readTT).trans (.of_eq ?_)
    rw [List.map_cons, List.map_cons, List.map_map]
    congr 1
    rw [targetKeptIs, List.map_map]
    exact List.map_congr_left fun component inTarget => targetItemsRead component inTarget
  have targetItemsMembers : Members ambientCoreCalc ambientBlock free (List.replicate owned nameType ++ bound)
      (((reacted.filter (placedAt target)).map (liftBVars 0 owned)).map readTT) := by
    have reading := (decode_typed (g + 4)).2.1 (liftBVars 0 owned target) elsewhere' elsewhere'Members
    rwa [readPlaced_succ, atTargetT] at reading
  have marker'ReadTyped : HasType ambientCoreCalc free (List.replicate owned nameType ++ bound)
      (readTT (liftBVars 0 owned marker')) procType :=
    targetItemsMembers _ (targetItemsPerm.symm.subset (List.mem_cons_self))
  have enteredSide : ProcEquiv ambientCoreCalc ambientBlock free bound
      (Prenex.restricts ambientBlock owned (readT (liftBVars 0 owned destination))) entered := by
    rw [destinationReadT]
    refine .trans _ _ _ (restricts_amb_equivalent owned targetNameTyped' (body_typed targetItemsMembers))
      (amb_fill targetNameTyped' ?_)
    refine .trans _ _ _ (restricts_congr (language := ambientCoreCalc) (block := ambientBlock) owned
      (body_perm_equivalent targetItemsMembers targetItemsPerm)) ?_
    refine .trans _ _ _ (restricts_body_middle (before := []) owned Members.nil targetMembers marker'ReadTyped) ?_
    exact body_congr (Members.cons (restricts_typed (language := ambientCoreCalc) (block := ambientBlock) owned
      marker'ReadTyped) targetMembers) (.cons movedSide (List.forall₂_same.mpr fun _ _ => .refl _))
  have hereFiltered : ((here.filter fun component => component != marker).map (liftBVars 0 owned)).map readT |>.Perm
      (readT (liftBVars 0 owned destination) :: (others.map readS).map (liftBVars 0 owned)) := by
    have filtered := hereSplit.filter fun component => component != marker
    have othersKept : others.filter (fun component => component != marker) = others :=
      List.filter_eq_self.mpr fun component inOthers => by
        have different : component ≠ marker := fun same => markerNotOthers (same ▸ inOthers)
        simp [different]
    rw [List.filter_cons_of_neg (by simp), List.filter_cons_of_pos (by simpa using markerDestination.symm),
      othersKept] at filtered
    refine ((filtered.map (liftBVars 0 owned)).map readT).trans (.of_eq ?_)
    rw [List.map_cons, List.map_cons, List.map_map, List.map_map]
    congr 1
    exact List.map_congr_left fun component inOthers => othersRead component inOthers
  have hereItemsMembers : Members ambientCoreCalc ambientBlock free (List.replicate owned nameType ++ bound)
      (((here.filter fun component => component != marker).map (liftBVars 0 owned)).map readT) := by
    have reading := (decode_typed (g + 6)).2.1 (liftBVars 0 owned parent) _ extended
    rwa [targetIs] at reading
  have destinationReadTyped : HasType ambientCoreCalc free (List.replicate owned nameType ++ bound)
      (readT (liftBVars 0 owned destination)) procType :=
    hereItemsMembers _ (hereFiltered.symm.subset (List.mem_cons_self))
  have targetSide : ProcEquiv ambientCoreCalc ambientBlock free bound
      (Prenex.restricts ambientBlock owned (Prenex.body ambientBlock
        (((here.filter fun component => component != marker).map (liftBVars 0 owned)).map readT)))
      (Prenex.body ambientBlock (entered :: others.map readS)) := by
    refine .trans _ _ _ (restricts_congr (language := ambientCoreCalc) (block := ambientBlock) owned
      (body_perm_equivalent hereItemsMembers hereFiltered)) ?_
    refine .trans _ _ _ (restricts_body_middle (before := []) owned Members.nil othersMembers destinationReadTyped) ?_
    exact body_congr (Members.cons (restricts_typed (language := ambientCoreCalc) (block := ambientBlock) owned
      destinationReadTyped) othersMembers) (.cons enteredSide (List.forall₂_same.mpr fun _ _ => .refl _))
  -- the source side: the stepped items, unpadded and regrouped
  have paddedRelated : ∀ items : List Pattern, Members ambientCoreCalc ambientBlock free bound items →
      (∀ item ∈ items, isObjectPattern item = true) →
      List.Forall₂ (ProcEquiv ambientCoreCalc ambientBlock free bound) (items.map padA) items := by
    intro items itemsMembers itemsObjects
    refine List.forall₂_map_left_iff.mpr (List.forall₂_same.mpr fun item inItems => ?_)
    exact Relation.EqvGen.symm _ _ (padA_equivalent (size item + 1) (Nat.lt_succ_self _)
      (itemsMembers item inItems) (itemsObjects item inItems))
  have paddedMembers : ∀ items : List Pattern, Members ambientCoreCalc ambientBlock free bound items →
      (∀ item ∈ items, isObjectPattern item = true) → Members ambientCoreCalc ambientBlock free bound (items.map padA) :=
    fun items itemsMembers itemsObjects item inItems => by
      obtain ⟨original, inOriginal, rfl⟩ := List.mem_map.mp inItems
      exact padA_typed (itemsMembers original inOriginal) (itemsObjects original inOriginal)
  have erasedIs : ((atMover.map readM).map padA).eraseIdx k = ((atMover.eraseIdx k).map readM).map padA := by
    rw [List.eraseIdx_map, List.eraseIdx_map]
  have erasedPerm : ((atMover.eraseIdx k).map readM).Perm moverKept := by
    have perm := eraseIdx_perm_erase hk
    rw [capabilityAtK] at perm
    exact perm.map readM
  have erasedMembers : Members ambientCoreCalc ambientBlock free bound ((atMover.eraseIdx k).map readM) :=
    fun item inItems => moverKeptMembers item (erasedPerm.subset inItems)
  have erasedObjects : ∀ item ∈ (atMover.eraseIdx k).map readM, isObjectPattern item = true := fun item inItems => by
    obtain ⟨original, inErased, rfl⟩ := List.mem_map.mp inItems
    exact moverObjects _ (List.mem_map_of_mem (List.mem_of_mem_eraseIdx inErased))
  have innerMembers : Members ambientCoreCalc ambientBlock free bound
      (padA continuationRead :: ((atMover.eraseIdx k).map readM).map padA) :=
    Members.cons (padA_typed continuationTyped continuationObject)
      (paddedMembers _ erasedMembers erasedObjects)
  have innerSide : ProcEquiv ambientCoreCalc ambientBlock free bound
      (.collection .hashBag (padA continuationRead :: ((atMover.map readM).map padA).eraseIdx k) none)
      movedContent := by
    rw [erasedIs]
    refine .trans _ _ _ (bag_body_equivalent (language := ambientCoreCalc) (block := ambientBlock) innerMembers) ?_
    refine .trans _ _ _ (body_congr innerMembers (.cons (Relation.EqvGen.symm _ _
      (padA_equivalent (size continuationRead + 1) (Nat.lt_succ_self _) continuationTyped continuationObject))
      (paddedRelated _ erasedMembers erasedObjects))) ?_
    exact body_perm_equivalent (Members.cons continuationTyped erasedMembers) (erasedPerm.cons _)
  have hostSide : ProcEquiv ambientCoreCalc ambientBlock free bound (asBag (padA targetContent))
      (Prenex.body ambientBlock targetKept) := by
    have contentTyped : HasType ambientCoreCalc free bound targetContent procType := by
      rw [targetContentIs']
      exact body_typed targetMembers
    have contentObject : isObjectPattern targetContent = true := by
      rw [targetContentIs']
      exact Mettapedia.GSLT.LanguageDef.RestrictionBlocks.isObject_toPattern (form := ⟨0, targetKept⟩)
        (fun item inItems => targetObjects item inItems)
    refine Relation.EqvGen.symm _ _ (.trans _ _ _ ?_ (asBag_equivalent (padA_typed contentTyped contentObject)))
    rw [← targetContentIs']
    exact padA_equivalent (size targetContent + 1) (Nat.lt_succ_self _) contentTyped contentObject
  have movedPadded : HasType ambientCoreCalc free bound
      (amb moverName (.collection .hashBag (padA continuationRead :: ((atMover.map readM).map padA).eraseIdx k) none))
      procType := by
    rw [erasedIs]
    exact amb_typed moverNameTyped' ((Mettapedia.GSLT.LanguageDef.RestrictionBlocks.SortedEquiv.typed_iff
      (bag_body_equivalent (language := ambientCoreCalc) (block := ambientBlock) innerMembers)).mpr
      (body_typed innerMembers))
  have hostTyped : HasType ambientCoreCalc free bound (asBag (padA targetContent)) procType :=
    (Mettapedia.GSLT.LanguageDef.RestrictionBlocks.SortedEquiv.typed_iff hostSide).mpr (body_typed targetMembers)
  have pairMembers : Members ambientCoreCalc ambientBlock free bound
      [amb moverName (.collection .hashBag (padA continuationRead :: ((atMover.map readM).map padA).eraseIdx k) none),
        asBag (padA targetContent)] :=
    Members.cons movedPadded (Members.cons hostTyped Members.nil)
  have enteredPadded : ProcEquiv ambientCoreCalc ambientBlock free bound
      (amb targetName (.collection .hashBag
        [amb moverName (.collection .hashBag (padA continuationRead :: ((atMover.map readM).map padA).eraseIdx k) none),
          asBag (padA targetContent)] none)) entered := by
    refine amb_fill targetNameTyped' ?_
    refine .trans _ _ _ (body_congr (first := [_, _]) (second := [moved, Prenex.body ambientBlock targetKept])
      pairMembers (.cons (amb_fill moverNameTyped' innerSide) (.cons hostSide .nil))) ?_
    exact body_pair_equivalent (first := [moved]) (Members.cons movedTyped Members.nil) targetMembers
  have sourceMembers : Members ambientCoreCalc ambientBlock free bound
      (amb targetName (.collection .hashBag
        [amb moverName (.collection .hashBag (padA continuationRead :: ((atMover.map readM).map padA).eraseIdx k) none),
          asBag (padA targetContent)] none) :: others.map (padA ∘ readS)) := by
    refine Members.cons ((Mettapedia.GSLT.LanguageDef.RestrictionBlocks.SortedEquiv.typed_iff enteredPadded).mpr
      enteredTyped) ?_
    rw [← List.map_map]
    exact paddedMembers _ othersMembers othersObjects
  have sourceSide : ProcEquiv ambientCoreCalc ambientBlock free bound
      (.collection .hashBag (amb targetName (.collection .hashBag
        [amb moverName (.collection .hashBag (padA continuationRead :: ((atMover.map readM).map padA).eraseIdx k) none),
          asBag (padA targetContent)] none) :: others.map (padA ∘ readS)) none)
      (Prenex.body ambientBlock (entered :: others.map readS)) := by
    refine .trans _ _ _ (bag_body_equivalent (language := ambientCoreCalc) (block := ambientBlock) sourceMembers) ?_
    refine body_congr sourceMembers (.cons enteredPadded ?_)
    rw [← List.map_map]
    exact paddedRelated _ othersMembers othersObjects
  exact .trans _ _ _ sourceSide (Relation.EqvGen.symm _ _ targetSide)

/-! ## Leaving at its place -/

/-- **An exit read at the place of the ambient left reads as an exit there**: the ambient left, holding the moving
ambient with the capability in it, steps to the moved ambient beside what is left of it, which is what the reacted
components read as there, under the continuation's restrictions. -/
theorem exit_local {bound : List TypeExpr} {count : Nat} {components : List Pattern} {depth : Nat → Nat}
    (children : ∀ component ∈ components, ∀ child, childOf component = some child →
      ∃ index < count, child = .bvar index)
    (grows : ∀ component ∈ components, ∀ index child, index < count → child < count →
      placeAt component = some (.bvar index) → childOf component = some (.bvar child) → depth index < depth child)
    (unique : ∀ child, (components.filter fun component => childOf component == some child).length ≤ 1)
    (typed : Members locatedCalc locatedBlock free bound components)
    {parent mover target moverName targetName continuation : Pattern} {owned : Nat} {group : List Pattern}
    (moverNameVar : isVariable moverName = true) (targetNameVar : isVariable targetName = true)
    (decomposed : decompose locatedBlock continuation = ⟨owned, group⟩)
    (groupPlaced : ∀ component ∈ group, ∀ at', placeAt component = some at' →
      at' = liftBVars 0 owned mover ∨ ∃ index < owned, at' = .bvar index)
    (groupChildren : ∀ component ∈ group, ∀ child, childOf component = some child →
      ∃ index < owned, child = .bvar index)
    (groupTyped : Members locatedCalc locatedBlock free (List.replicate owned nameType ++ bound) group)
    {list : List Pattern} (sub : list.Sublist components)
    (markerIn : Pattern.apply "LAmb" [target, mover, moverName] ∈ list)
    (capabilityIn : Pattern.apply "LOut" [mover, targetName, continuation] ∈ list)
    (destinationIn : Pattern.apply "LAmb" [parent, target, targetName] ∈ list)
    (fuel : Nat) (enough : 3 * sizeList list + 6 ≤ fuel) :
    ∃ result, AmbNuRawStep (.collection .hashBag ((readPlaced fuel parent list).map padA) none) result ∧
      ProcEquiv ambientCoreCalc ambientBlock free bound result (Prenex.restricts ambientBlock owned
        (Prenex.body ambientBlock (readPlaced fuel (liftBVars 0 owned parent)
          ((reactList (.apply "LOut" [mover, targetName, continuation]) (.apply "LAmb" [target, mover, moverName])
            (.apply "LAmb" [parent, mover, moverName]) list).map (liftBVars 0 owned) ++ group)))) := by
  have within : ∀ component ∈ list, component ∈ components := fun component inList => sub.subset inList
  obtain ⟨g, rfl⟩ : ∃ g, fuel = g + 6 := ⟨fuel - 6, by omega⟩
  set capability := Pattern.apply "LOut" [mover, targetName, continuation] with capabilityIs
  set marker := Pattern.apply "LAmb" [target, mover, moverName] with markerIs
  set marker' := Pattern.apply "LAmb" [parent, mover, moverName] with marker'Is
  set destination := Pattern.apply "LAmb" [parent, target, targetName] with destinationIs
  have outListed : "LOut" ∈ capabilities := by simp [capabilities]
  have ambMarker : "LAmb" ∈ markers := by simp [markers]
  have capabilityAt : placeAt capability = some mover := placeAt_capability outListed _ _ _
  have markerAt : placeAt marker = some target := placeAt_ofMarker ambMarker _ _ _
  have marker'At : placeAt marker' = some parent := placeAt_ofMarker ambMarker _ _ _
  have destinationAt : placeAt destination = some parent := placeAt_ofMarker ambMarker _ _ _
  have markerChild : childOf marker = some mover := by simp [markerIs, childOf, markers]
  have destinationChild : childOf destination = some target := by simp [destinationIs, childOf, markers]
  have moverTarget : mover ≠ target :=
    child_ne_place children grows (within _ markerIn) (by simp [placedAt, markerAt]) markerChild
  have targetParent : target ≠ parent :=
    child_ne_place children grows (within _ destinationIn) (by simp [placedAt, destinationAt]) destinationChild
  have moverParent : mover ≠ parent := fun same =>
    not_reaches_up_two children grows within (within _ destinationIn) destinationAt destinationChild
      (within _ markerIn) markerAt markerChild (by rw [same]; exact Reaches.here)
  have uniqueList : ∀ child, (list.filter fun component => childOf component == some child).length ≤ 1 :=
    fun child => le_trans (sub.filter _).length_le (unique child)
  have onlyMarker : ∀ component ∈ list, childOf component = some mover → component = marker :=
    fun component member isChild => eq_of_filter_length_le_one (uniqueList mover) member markerIn
      (by simp [isChild]) (by simp [markerChild])
  have onlyDestination : ∀ component ∈ list, childOf component = some target → component = destination :=
    fun component member isChild => eq_of_filter_length_le_one (uniqueList target) member destinationIn
      (by simp [isChild]) (by simp [destinationChild])
  -- at the place: the ambient left among the components there
  set here := list.filter (placedAt parent) with hereIs
  set elsewhere := list.filter fun other => !placedAt parent other with elsewhereIs
  have destinationHere : destination ∈ here := List.mem_filter.mpr ⟨destinationIn, by simp [placedAt, destinationAt]⟩
  have markerElsewhere : marker ∈ elsewhere :=
    List.mem_filter.mpr ⟨markerIn, by simp [placedAt, markerAt, targetParent]⟩
  have capabilityElsewhere : capability ∈ elsewhere :=
    List.mem_filter.mpr ⟨capabilityIn, by simp [placedAt, capabilityAt, moverParent]⟩
  have destinationNotElsewhere : destination ∉ elsewhere := fun inElsewhere => by
    simp [elsewhereIs, placedAt, destinationAt] at inElsewhere
  obtain ⟨pos, hpos, destinationAtPos⟩ := List.getElem_of_mem destinationHere
  set others := here.eraseIdx pos with othersIs
  have hereSplit : here.Perm (destination :: others) := by
    have split := (List.getElem_cons_eraseIdx_perm hpos).symm
    rwa [destinationAtPos] at split
  have hereSub : here.Sublist components := List.filter_sublist.trans sub
  have destinationNotOthers : destination ∉ others :=
    not_mem_of_perm_unique (le_trans (hereSub.filter _).length_le (unique target)) hereSplit
      (by simp [destinationChild])
  have othersHere : ∀ component ∈ others, component ∈ here := fun component inOthers =>
    hereSplit.symm.subset (List.mem_cons_of_mem _ inOthers)
  -- in the ambient left: the moving ambient among its components
  set atTarget := elsewhere.filter (placedAt target) with atTargetIs
  set besideTarget := elsewhere.filter fun other => !placedAt target other with besideTargetIs
  have markerAtTarget : marker ∈ atTarget := List.mem_filter.mpr ⟨markerElsewhere, by simp [placedAt, markerAt]⟩
  have markerNotBeside : marker ∉ besideTarget := fun inBeside => by
    simp [besideTargetIs, placedAt, markerAt] at inBeside
  have capabilityBeside : capability ∈ besideTarget :=
    List.mem_filter.mpr ⟨capabilityElsewhere, by simp [placedAt, capabilityAt, moverTarget]⟩
  obtain ⟨i, hi, markerAtI⟩ := List.getElem_of_mem markerAtTarget
  have atTargetSub : atTarget.Sublist components := (List.filter_sublist.trans List.filter_sublist).trans sub
  have targetSplit : atTarget.Perm (marker :: atTarget.eraseIdx i) := by
    have split := (List.getElem_cons_eraseIdx_perm hi).symm
    rwa [markerAtI] at split
  have markerOnceTarget : marker ∉ atTarget.eraseIdx i :=
    not_mem_of_perm_unique (le_trans (atTargetSub.filter _).length_le (unique mover)) targetSplit
      (by simp [markerChild])
  -- in the moving ambient: the capability among its components
  set atMover := besideTarget.filter (placedAt mover) with atMoverIs
  set besideMover := besideTarget.filter fun other => !placedAt mover other with besideMoverIs
  have capabilityAtMover : capability ∈ atMover :=
    List.mem_filter.mpr ⟨capabilityBeside, by simp [placedAt, capabilityAt]⟩
  obtain ⟨k, hk, capabilityAtK⟩ := List.getElem_of_mem capabilityAtMover
  -- weights
  have elsewhereSize : sizeList elsewhere + 4 ≤ sizeList list := by
    have split : size destination + sizeList elsewhere ≤ sizeList list := size_add_elsewhere destinationHere
    have destinationSize : 4 ≤ size destination := by
      simp only [destinationIs, size, sizeList]
      have := size_pos parent
      have := size_pos target
      have := size_pos targetName
      omega
    omega
  have besideSize : sizeList besideTarget + 4 ≤ sizeList elsewhere := by
    have split : size marker + sizeList besideTarget ≤ sizeList elsewhere := size_add_elsewhere markerAtTarget
    have markerSize : 4 ≤ size marker := by
      simp only [markerIs, size, sizeList]
      have := size_pos target
      have := size_pos mover
      have := size_pos moverName
      omega
    omega
  -- the source: the exit inside the ambient left, among the padded items at the place
  set readS := fun component => readComponent (g + 5) parent component elsewhere with readSIs
  have sourceIs : (readPlaced (g + 6) parent list).map padA = here.map (padA ∘ readS) := by
    rw [readPlaced_succ, List.map_map]
  set readTS := fun component => readComponent (g + 3) target component besideTarget with readTSIs
  have targetContent : readPlaced (g + 4) target elsewhere = atTarget.map readTS := by
    rw [readPlaced_succ]
  have destinationRead : (padA ∘ readS) destination =
      .apply "AAmb" [targetName, .collection .hashBag ((atTarget.map readTS).map padA) none] := by
    simp only [Function.comp, readSIs]
    rw [padded_amb (g + 3) parent targetNameVar markerElsewhere (by simp [placedAt, markerAt])
      (fun _ _ _ => by simp [markerIs]), targetContent]
  have hposItems : pos < (here.map (padA ∘ readS)).length := by simpa using hpos
  have destinationItem : (here.map (padA ∘ readS))[pos] =
      amb targetName (.collection .hashBag ((atTarget.map readTS).map padA) none) := by
    rw [List.getElem_map, destinationAtPos, destinationRead]
    rfl
  have settledMover : readPlaced (g + 2) mover besideTarget = readPlaced (g + 4) mover besideTarget :=
    readPlaced_settled mover besideTarget (by omega) (by omega)
  set readM := fun component => readComponent (g + 3) mover component besideMover with readMIs
  have moverContent : readPlaced (g + 4) mover besideTarget = atMover.map readM := by
    rw [readPlaced_succ]
  have moverRead : padA (readTS marker) =
      .apply "AAmb" [moverName, .collection .hashBag ((atMover.map readM).map padA) none] := by
    simp only [readTSIs]
    rw [padded_amb (g + 1) target moverNameVar capabilityBeside (by simp [placedAt, capabilityAt])
      (fun _ _ _ => by simp [capabilityIs]), settledMover, moverContent]
  set continuationRead := Prenex.toPattern ambientBlock
    (decodeForm (g + 2) mover (decompose locatedBlock continuation)) with continuationReadIs
  have capabilityRead : padA (readM capability) = .apply "AOut" [targetName, padA continuationRead] := by
    simp only [readMIs, capabilityIs]
    rw [readComponent_capability (g + 2) mover outListed targetNameVar, show ambientCapability "LOut" = "AOut" by decide,
      padA_capability (by decide) targetNameVar]
  have hkInner : k < ((atMover.map readM).map padA).length := by simpa using hk
  have capabilityItem : ((atMover.map readM).map padA)[k] = .apply "AOut" [targetName, padA continuationRead] := by
    rw [List.getElem_map, List.getElem_map, capabilityAtK, capabilityRead]
  have hiContents : i < ((atTarget.map readTS).map padA).length := by simpa using hi
  have moverItem : ((atTarget.map readTS).map padA)[i] =
      amb moverName (.collection .hashBag ((atMover.map readM).map padA) none) := by
    rw [List.getElem_map, List.getElem_map, markerAtI, moverRead]
    rfl
  have innerStep := AmbNuRawStep.exit (tail := none) i hiContents moverName targetName (padA continuationRead) k
    hkInner moverItem capabilityItem
  have step := AmbNuRawStep.par (tail := none) pos hposItems (by rw [destinationItem]; exact innerStep)
  have restIs : (here.map (padA ∘ readS)).eraseIdx pos = others.map (padA ∘ readS) := List.eraseIdx_map _ _ _
  rw [restIs] at step
  rw [sourceIs]
  refine ⟨_, step, ?_⟩
  -- the reacted components, place by place
  set reacted := reactList capability marker marker' list with reactedIs
  have capabilityMarker : capability ≠ marker := by simp [capabilityIs, markerIs]
  have markerOnceList : marker ∉ list.erase marker :=
    not_mem_of_perm_unique (uniqueList mover) (List.perm_cons_erase markerIn) (by simp [markerChild])
  have reactedHere : (reacted.filter (placedAt parent)).Perm (marker' :: here) :=
    reactList_filter_arrives (keep := placedAt parent) (marker' := marker')
      (by simp [placedAt, capabilityAt, moverParent]) (by simp [placedAt, markerAt, targetParent])
      (by simp [placedAt, marker'At]) markerIn markerOnceList capabilityMarker
  have reactedAtTarget : reacted.filter (placedAt target) = atTarget.filter fun component => component != marker := by
    rw [reactedIs, reactList_filter_leaves (by simp [placedAt, capabilityAt, moverTarget])
      (by simp [placedAt, marker'At, Ne.symm targetParent]), atTargetIs, filter_at_elsewhere targetParent]
  have reactedAtMover : reacted.filter (placedAt mover) = atMover.erase capability := by
    rw [reactedIs, reactList_filter (show placedAt mover marker' = placedAt mover marker by
      simp [placedAt, marker'At, markerAt, Ne.symm moverParent, Ne.symm moverTarget])]
    rw [reactList_of_not_mem (fun inFiltered => by simp [placedAt, markerAt, Ne.symm moverTarget] at inFiltered),
      atMoverIs, besideTargetIs, filter_at_elsewhere moverTarget, filter_at_elsewhere moverParent]
  have reactedAway : ∀ {at' : Pattern}, at' ≠ parent → at' ≠ mover → at' ≠ target →
      reacted.filter (placedAt at') = list.filter (placedAt at') := fun awayParent awayMover awayTarget =>
    reactList_at (by simp [placedAt, capabilityAt, Ne.symm awayMover])
      (by simp [placedAt, markerAt, Ne.symm awayTarget]) (by simp [placedAt, marker'At, Ne.symm awayParent])
  -- the target's lists
  set elsewhere' := (reacted.filter fun other => !placedAt parent other).map (liftBVars 0 owned) ++ group
    with elsewhere'Is
  set besideT' := elsewhere'.filter fun other => !placedAt (liftBVars 0 owned target) other with besideT'Is
  set besideM' := elsewhere'.filter fun other => !placedAt (liftBVars 0 owned mover) other with besideM'Is
  set groupHere := group.filter (placedAt (liftBVars 0 owned mover)) with groupHereIs
  set groupDeep := group.filter fun other => !placedAt (liftBVars 0 owned mover) other with groupDeepIs
  have liftApart : ∀ {first second : Pattern}, first ≠ second →
      liftBVars 0 owned first ≠ liftBVars 0 owned second := fun different same =>
    different (liftBVars_injective owned same)
  set readT := fun component => readComponent (g + 5) (liftBVars 0 owned parent) component elsewhere' with readTIs
  have hereT : (reacted.map (liftBVars 0 owned) ++ group).filter (placedAt (liftBVars 0 owned parent)) =
      (reacted.filter (placedAt parent)).map (liftBVars 0 owned) := by
    rw [List.filter_append, filter_lift_at, group_filter_apart groupPlaced (Ne.symm moverParent), List.append_nil]
  have elsewhereT : (reacted.map (liftBVars 0 owned) ++ group).filter
      (fun other => !placedAt (liftBVars 0 owned parent) other) = elsewhere' := by
    rw [List.filter_append, filter_lift_elsewhere, group_filter_beside groupPlaced (Ne.symm moverParent)]
  have targetIs : readPlaced (g + 6) (liftBVars 0 owned parent) (reacted.map (liftBVars 0 owned) ++ group) =
      ((reacted.filter (placedAt parent)).map (liftBVars 0 owned)).map readT := by
    rw [readPlaced_succ, hereT, elsewhereT]
  rw [targetIs]
  set readMM := fun component => readComponent (g + 3) (liftBVars 0 owned mover) component besideM' with readMMIs
  have atMoverT : elsewhere'.filter (placedAt (liftBVars 0 owned mover)) =
      (atMover.erase capability).map (liftBVars 0 owned) ++ groupHere := by
    rw [elsewhere'Is, List.filter_append, filter_lift_at, filter_at_elsewhere moverParent, reactedAtMover]
  have liftedMarker' : liftBVars 0 owned marker' = .apply "LAmb"
      [liftBVars 0 owned parent, liftBVars 0 owned mover, liftBVars 0 owned moverName] := by
    simp [marker'Is, liftBVars, Mettapedia.OSLF.MeTTaIL.Substitution.liftBVarsList_eq_map]
  have marker'ReadT : readT (liftBVars 0 owned marker') = .apply "AAmb" [liftBVars 0 owned moverName,
      Prenex.body ambientBlock (((atMover.erase capability).map (liftBVars 0 owned) ++ groupHere).map readMM)] := by
    simp only [readTIs]
    rw [liftedMarker', readComponent_amb (g + 4) _ (by rw [isVariable_lift]; exact moverNameVar), readPlaced_succ,
      atMoverT]
  set readTT := fun component => readComponent (g + 3) (liftBVars 0 owned target) component besideT' with readTTIs
  have atTargetT : elsewhere'.filter (placedAt (liftBVars 0 owned target)) =
      (atTarget.filter fun component => component != marker).map (liftBVars 0 owned) := by
    rw [elsewhere'Is, List.filter_append, filter_lift_at, filter_at_elsewhere targetParent, reactedAtTarget,
      group_filter_apart groupPlaced (Ne.symm moverTarget), List.append_nil]
  have liftedDestination : liftBVars 0 owned destination = .apply "LAmb"
      [liftBVars 0 owned parent, liftBVars 0 owned target, liftBVars 0 owned targetName] := by
    simp [destinationIs, liftBVars, Mettapedia.OSLF.MeTTaIL.Substitution.liftBVarsList_eq_map]
  have destinationReadT : readT (liftBVars 0 owned destination) = .apply "AAmb" [liftBVars 0 owned targetName,
      Prenex.body ambientBlock (((atTarget.filter fun component => component != marker).map
        (liftBVars 0 owned)).map readTT)] := by
    simp only [readTIs]
    rw [liftedDestination, readComponent_amb (g + 4) _ (by rw [isVariable_lift]; exact targetNameVar),
      readPlaced_succ, atTargetT]
  have deepestIs : besideM' = ((reacted.filter fun other => !placedAt parent other).filter
      fun other => !placedAt mover other).map (liftBVars 0 owned) ++ groupDeep := by
    rw [besideM'Is, elsewhere'Is, List.filter_append, filter_lift_elsewhere]
  -- the continuation, read at the mover's location
  have groupDeepChildren : ∀ component ∈ groupDeep, ∀ child, childOf component = some child →
      ∃ index < owned, child = .bvar index := fun component inDeep =>
    groupChildren component (List.mem_filter.mp inDeep).1
  have groupRead : ∀ component ∈ groupHere,
      readMM component = readComponent (g + 3) (liftBVars 0 owned mover) component groupDeep := by
    intro component inHere'
    simp only [readMMIs]
    rw [deepestIs]
    exact group_reads groupDeepChildren (lifted_apart owned _) (g + 3) _ component
      (groupChildren component (List.mem_filter.mp inHere').1)
  have massBound : 3 * Prenex.mass ⟨owned, group⟩ + 3 ≤ g + 2 := by
    have massLe := Mettapedia.GSLT.LanguageDef.RestrictionBlocks.mass_decompose (block := locatedBlock) continuation
    rw [decomposed] at massLe
    have capabilitySize : size continuation + 3 ≤ size capability := by
      simp only [capabilityIs, size, sizeList]
      have := size_pos mover
      have := size_pos targetName
      omega
    have listSize := size_le_sizeList capabilityBeside
    omega
  have continuationIs : continuationRead = Prenex.restricts ambientBlock owned (Prenex.body ambientBlock
      (groupHere.map fun component => readComponent (g + 3) (liftBVars 0 owned mover) component groupDeep)) := by
    rw [continuationReadIs, decomposed, decodeForm_settled mover _ massBound (show 3 * _ + 3 ≤ g + 5 by omega)]
    simp only [decodeForm, Prenex.toPattern]
    rw [readPlaced_succ]
  -- the untouched components read as before, lifted
  have elsewhereWithin : ∀ component ∈ elsewhere, component ∈ components := fun component inElsewhere =>
    within component (List.mem_filter.mp inElsewhere).1
  have besideTargetWithin : ∀ component ∈ besideTarget, component ∈ components := fun component inBeside =>
    elsewhereWithin component (List.mem_filter.mp inBeside).1
  have besideMoverWithin : ∀ component ∈ besideMover, component ∈ components := fun component inBeside =>
    besideTargetWithin component (List.mem_filter.mp inBeside).1
  have noTargetChild : ∀ component ∈ elsewhere, childOf component ≠ some target := fun component inElsewhere isChild =>
    destinationNotElsewhere (onlyDestination component (List.mem_filter.mp inElsewhere).1 isChild ▸ inElsewhere)
  have noMoverChild : ∀ component ∈ besideTarget, childOf component ≠ some mover := fun component inBeside isChild =>
    markerNotBeside (onlyMarker component
      (List.mem_filter.mp (List.mem_filter.mp inBeside).1).1 isChild ▸ inBeside)
  have changedAt : ∀ {at' : Pattern}, at' ≠ parent → at' ≠ mover → at' ≠ target →
      elsewhere'.filter (placedAt (liftBVars 0 owned at')) = (list.filter (placedAt at')).map (liftBVars 0 owned) := by
    intro at' awayParent awayMover awayTarget
    rw [elsewhere'Is, List.filter_append, filter_lift_at, filter_at_elsewhere awayParent,
      reactedAway awayParent awayMover awayTarget, group_filter_apart groupPlaced awayMover, List.append_nil]
  have changedAtT : ∀ {at' : Pattern}, at' ≠ parent → at' ≠ mover → at' ≠ target →
      besideT'.filter (placedAt (liftBVars 0 owned at')) = (list.filter (placedAt at')).map (liftBVars 0 owned) := by
    intro at' awayParent awayMover awayTarget
    rw [besideT'Is, filter_at_elsewhere (liftApart awayTarget), changedAt awayParent awayMover awayTarget]
  have changedAtM : ∀ {at' : Pattern}, at' ≠ parent → at' ≠ mover → at' ≠ target →
      besideM'.filter (placedAt (liftBVars 0 owned at')) = (list.filter (placedAt at')).map (liftBVars 0 owned) := by
    intro at' awayParent awayMover awayTarget
    rw [besideM'Is, filter_at_elsewhere (liftApart awayMover), changedAt awayParent awayMover awayTarget]
  have othersRead : ∀ component ∈ others,
      readT (liftBVars 0 owned component) = liftBVars 0 owned (readS component) := by
    intro component inOthers
    have inHere := othersHere component inOthers
    have member := (List.mem_filter.mp inHere).1
    have placed : placeAt component = some parent := by simpa [placedAt] using (List.mem_filter.mp inHere).2
    refine readComponent_lift_congr (g + 5) fun child isChild at' reached => ?_
    have childNotTarget : child ≠ target := fun same =>
      destinationNotOthers (onlyDestination component member (same ▸ isChild) ▸ inOthers)
    have awayParent : at' ≠ parent := fun same =>
      not_reaches_up children grows elsewhereWithin (within _ member) placed isChild (same ▸ reached)
    have awayTarget : at' ≠ target := fun same =>
      not_reaches_unmarked noTargetChild childNotTarget (same ▸ reached)
    have awayMover : at' ≠ mover := fun same => by
      have toMover : Reaches elsewhere child mover := same ▸ reached
      have childNotMover : child ≠ mover := fun same' => by
        have isMarker := onlyMarker component member (same' ▸ isChild)
        rw [isMarker, markerAt] at placed
        exact targetParent (Option.some.inj placed)
      obtain ⟨last, lastIn, lastChild, at'', lastPlaced, reachedLast⟩ := Reaches.penultimate toMover childNotMover
      rw [onlyMarker last (List.mem_filter.mp lastIn).1 lastChild, markerAt] at lastPlaced
      obtain rfl := Option.some.inj lastPlaced
      exact not_reaches_unmarked noTargetChild childNotTarget reachedLast
    rw [changedAt awayParent awayMover awayTarget, filter_at_elsewhere awayParent]
  have targetItemsRead : ∀ component ∈ atTarget, component ≠ marker →
      readTT (liftBVars 0 owned component) = liftBVars 0 owned (readTS component) := by
    intro component inTarget different
    have inElsewhere := (List.mem_filter.mp inTarget).1
    have member := (List.mem_filter.mp inElsewhere).1
    have placed : placeAt component = some target := by simpa [placedAt] using (List.mem_filter.mp inTarget).2
    refine readComponent_lift_congr (g + 3) fun child isChild at' reached => ?_
    have awayTarget : at' ≠ target := fun same =>
      not_reaches_up children grows besideTargetWithin (within _ member) placed isChild (same ▸ reached)
    have awayParent : at' ≠ parent := fun same =>
      not_reaches_up_two children grows besideTargetWithin (within _ destinationIn) destinationAt destinationChild
        (within _ member) placed isChild (same ▸ reached)
    have awayMover : at' ≠ mover := fun same => by
      refine not_reaches_unmarked noMoverChild (fun same' => ?_) (same ▸ reached)
      exact different (onlyMarker component member (same' ▸ isChild))
    rw [changedAtT awayParent awayMover awayTarget, besideTargetIs, filter_at_elsewhere awayTarget,
      filter_at_elsewhere awayParent]
  have moverItemsRead : ∀ component ∈ atMover,
      readMM (liftBVars 0 owned component) = liftBVars 0 owned (readM component) := by
    intro component inMover
    have inBeside := (List.mem_filter.mp inMover).1
    have inElsewhere := (List.mem_filter.mp inBeside).1
    have member := (List.mem_filter.mp inElsewhere).1
    have placed : placeAt component = some mover := by simpa [placedAt] using (List.mem_filter.mp inMover).2
    refine readComponent_lift_congr (g + 3) fun child isChild at' reached => ?_
    have awayMover : at' ≠ mover := fun same =>
      not_reaches_up children grows besideMoverWithin (within _ member) placed isChild (same ▸ reached)
    have awayTarget : at' ≠ target := fun same =>
      not_reaches_up_two children grows besideMoverWithin (within _ markerIn) markerAt markerChild
        (within _ member) placed isChild (same ▸ reached)
    have awayParent : at' ≠ parent := fun same =>
      not_reaches_up_three children grows besideMoverWithin (within _ destinationIn) destinationAt destinationChild
        (within _ markerIn) markerAt markerChild (within _ member) placed isChild (same ▸ reached)
    rw [changedAtM awayParent awayMover awayTarget, besideMoverIs, filter_at_elsewhere awayMover, besideTargetIs,
      filter_at_elsewhere awayTarget, filter_at_elsewhere awayParent]
  -- typing
  have listMembers : Members locatedCalc locatedBlock free bound list := fun component inList =>
    typed component (within component inList)
  have elsewhereMembers : Members locatedCalc locatedBlock free bound elsewhere := fun component inElsewhere =>
    listMembers component (List.mem_filter.mp inElsewhere).1
  have besideTargetMembers : Members locatedCalc locatedBlock free bound besideTarget := fun component inBeside =>
    elsewhereMembers component (List.mem_filter.mp inBeside).1
  have nameTypes : ∀ {place child name : Pattern}, Pattern.apply "LAmb" [place, child, name] ∈ list →
      HasType locatedCalc free bound child nameType ∧ HasType locatedCalc free bound name nameType := by
    intro place child name member
    rcases triple_inv (listMembers _ member) with ⟨-, second, third⟩ | ⟨listed, -, -⟩ | ⟨isCap, -, -⟩
    · exact ⟨second, third⟩
    · simp [capabilities] at listed
    · simp at isCap
  obtain ⟨moverTyped, moverNameTyped⟩ := nameTypes markerIn
  obtain ⟨-, targetNameTyped⟩ := nameTypes destinationIn
  have parentTyped : HasType locatedCalc free bound parent nameType :=
    triple_first (listMembers _ destinationIn)
  have marker'Typed : HasType locatedCalc free bound marker' procType :=
    Mettapedia.Languages.ProcessCalculi.Ambient.Encoding.marker_typed parentTyped moverTyped moverNameTyped
  have moverNameTyped' : HasType ambientCoreCalc free bound moverName nameType :=
    variable_typed moverNameTyped moverNameVar
  have targetNameTyped' : HasType ambientCoreCalc free bound targetName nameType :=
    variable_typed targetNameTyped targetNameVar
  have reactedMembers : Members locatedCalc locatedBlock free bound reacted := by
    intro component inReacted
    rcases mem_reactList inReacted with inList | rfl
    · exact listMembers component inList
    · exact marker'Typed
  have extended : Members locatedCalc locatedBlock free (List.replicate owned nameType ++ bound)
      (reacted.map (liftBVars 0 owned) ++ group) := by
    have lifted := Mettapedia.GSLT.LanguageDef.RestrictionBlocks.Members.lift (language := locatedCalc)
      (block := locatedBlock) (List.replicate owned nameType) reactedMembers
    rw [List.length_replicate] at lifted
    exact lifted.append groupTyped
  have elsewhere'Members : Members locatedCalc locatedBlock free (List.replicate owned nameType ++ bound)
      elsewhere' := fun component inElsewhere' => extended component (by
        rw [← elsewhereT] at inElsewhere'
        exact (List.mem_filter.mp inElsewhere').1)
  have hereReadMembers : Members ambientCoreCalc ambientBlock free bound (here.map readS) := by
    have reading := (decode_typed (g + 6)).2.1 parent list listMembers
    rwa [readPlaced_succ] at reading
  have hereReadObjects : ∀ item ∈ here.map readS, isObjectPattern item = true := by
    have objects := (decode_object (g + 6)).2.1 parent list
    rwa [readPlaced_succ] at objects
  have othersMembers : Members ambientCoreCalc ambientBlock free bound (others.map readS) := fun item inItems => by
    obtain ⟨original, inOthers, rfl⟩ := List.mem_map.mp inItems
    exact hereReadMembers _ (List.mem_map_of_mem (othersHere original inOthers))
  have othersObjects : ∀ item ∈ others.map readS, isObjectPattern item = true := fun item inItems => by
    obtain ⟨original, inOthers, rfl⟩ := List.mem_map.mp inItems
    exact hereReadObjects _ (List.mem_map_of_mem (othersHere original inOthers))
  have targetReadMembers : Members ambientCoreCalc ambientBlock free bound (atTarget.map readTS) := by
    have reading := (decode_typed (g + 4)).2.1 target elsewhere elsewhereMembers
    rwa [targetContent] at reading
  have targetReadObjects : ∀ item ∈ atTarget.map readTS, isObjectPattern item = true := by
    have objects := (decode_object (g + 4)).2.1 target elsewhere
    rwa [targetContent] at objects
  have moverMembers : Members ambientCoreCalc ambientBlock free bound (atMover.map readM) := by
    have reading := (decode_typed (g + 4)).2.1 mover besideTarget besideTargetMembers
    rwa [moverContent] at reading
  have moverObjects : ∀ item ∈ atMover.map readM, isObjectPattern item = true := by
    have objects := (decode_object (g + 4)).2.1 mover besideTarget
    rwa [moverContent] at objects
  have continuationTyped : HasType ambientCoreCalc free bound continuationRead procType := by
    rw [continuationReadIs, decomposed]
    exact decodeForm_typed (g + 2) mover groupTyped
  have continuationObject : isObjectPattern continuationRead = true :=
    Mettapedia.GSLT.LanguageDef.RestrictionBlocks.isObject_toPattern ((decode_object (g + 2)).1 mover _)
  set moverKept := (atMover.erase capability).map readM with moverKeptIs
  have moverKeptMembers : Members ambientCoreCalc ambientBlock free bound moverKept := fun item inItems => by
    obtain ⟨original, inErased, rfl⟩ := List.mem_map.mp inItems
    exact moverMembers _ (List.mem_map_of_mem (List.mem_of_mem_erase inErased))
  set targetKept := (atTarget.filter fun component => component != marker).map readTS with targetKeptIs
  have targetKeptMembers : Members ambientCoreCalc ambientBlock free bound targetKept := fun item inItems => by
    obtain ⟨original, inFiltered, rfl⟩ := List.mem_map.mp inItems
    exact targetReadMembers _ (List.mem_map_of_mem (List.mem_filter.mp inFiltered).1)
  have groupReadMembers : Members ambientCoreCalc ambientBlock free (List.replicate owned nameType ++ bound)
      (groupHere.map fun component => readComponent (g + 3) (liftBVars 0 owned mover) component groupDeep) := by
    have reading := (decode_typed (g + 4)).2.1 (liftBVars 0 owned mover) group groupTyped
    rwa [readPlaced_succ] at reading
  -- the common form both sides are equivalent to
  set movedContent := Prenex.body ambientBlock (continuationRead :: moverKept) with movedContentIs
  set moved := Pattern.apply "AAmb" [moverName, movedContent] with movedIs
  set shrunk := Pattern.apply "AAmb" [targetName, Prenex.body ambientBlock targetKept] with shrunkIs
  have movedTyped : HasType ambientCoreCalc free bound moved procType :=
    amb_typed moverNameTyped' (body_typed (Members.cons continuationTyped moverKeptMembers))
  have shrunkTyped : HasType ambientCoreCalc free bound shrunk procType :=
    amb_typed targetNameTyped' (body_typed targetKeptMembers)
  -- the target side: the moved ambient takes the restrictions, the ambient left and the others read lifted
  have moverItemsIs : ((atMover.erase capability).map (liftBVars 0 owned) ++ groupHere).map readMM =
      moverKept.map (liftBVars 0 owned) ++
        groupHere.map fun component => readComponent (g + 3) (liftBVars 0 owned mover) component groupDeep := by
    rw [List.map_append, List.map_map, moverKeptIs, List.map_map]
    refine congrArg₂ (· ++ ·) (List.map_congr_left fun component inErased => ?_)
      (List.map_congr_left fun component inGroup => groupRead component inGroup)
    exact moverItemsRead component (List.mem_of_mem_erase inErased)
  have moverBodyTyped : HasType ambientCoreCalc free (List.replicate owned nameType ++ bound)
      (Prenex.body ambientBlock (((atMover.erase capability).map (liftBVars 0 owned) ++ groupHere).map readMM))
      procType := by
    have reading := (decode_typed (g + 4)).2.1 (liftBVars 0 owned mover) elsewhere' elsewhere'Members
    rw [readPlaced_succ, atMoverT] at reading
    exact body_typed reading
  have movedSide : ProcEquiv ambientCoreCalc ambientBlock free bound
      (Prenex.restricts ambientBlock owned (readT (liftBVars 0 owned marker'))) moved := by
    rw [marker'ReadT]
    refine .trans _ _ _ (restricts_amb_equivalent owned moverNameTyped' moverBodyTyped) (amb_fill moverNameTyped' ?_)
    rw [moverItemsIs, movedContentIs, continuationIs]
    exact restricts_body_split owned moverKeptMembers groupReadMembers
  have destinationLifted : readT (liftBVars 0 owned destination) = liftBVars 0 owned shrunk := by
    rw [destinationReadT, shrunkIs]
    have itemsIs : ((atTarget.filter fun component => component != marker).map (liftBVars 0 owned)).map readTT =
        targetKept.map (liftBVars 0 owned) := by
      rw [List.map_map, targetKeptIs, List.map_map]
      refine List.map_congr_left fun component inFiltered => ?_
      exact targetItemsRead component (List.mem_filter.mp inFiltered).1
        (by simpa using (List.mem_filter.mp inFiltered).2)
    rw [itemsIs, ← Mettapedia.GSLT.LanguageDef.RestrictionBlocks.liftBVars_body]
    simp [liftBVars, Mettapedia.OSLF.MeTTaIL.Substitution.liftBVarsList_eq_map]
  have hereItemsPerm : (((reacted.filter (placedAt parent)).map (liftBVars 0 owned)).map readT).Perm
      (readT (liftBVars 0 owned marker') :: (shrunk :: others.map readS).map (liftBVars 0 owned)) := by
    refine (((reactedHere.trans (hereSplit.cons _)).map (liftBVars 0 owned)).map readT).trans (.of_eq ?_)
    rw [List.map_cons, List.map_cons, List.map_cons, List.map_cons, destinationLifted, List.map_cons, List.map_map,
      List.map_map]
    congr 2
    exact List.map_congr_left fun component inOthers => othersRead component inOthers
  have hereItemsMembers : Members ambientCoreCalc ambientBlock free (List.replicate owned nameType ++ bound)
      (((reacted.filter (placedAt parent)).map (liftBVars 0 owned)).map readT) := by
    have reading := (decode_typed (g + 6)).2.1 (liftBVars 0 owned parent) _ extended
    rwa [targetIs] at reading
  have marker'ReadTyped : HasType ambientCoreCalc free (List.replicate owned nameType ++ bound)
      (readT (liftBVars 0 owned marker')) procType :=
    hereItemsMembers _ (hereItemsPerm.symm.subset (List.mem_cons_self))
  have keptMembers : Members ambientCoreCalc ambientBlock free bound (shrunk :: others.map readS) :=
    Members.cons shrunkTyped othersMembers
  have targetSide : ProcEquiv ambientCoreCalc ambientBlock free bound
      (Prenex.restricts ambientBlock owned (Prenex.body ambientBlock
        (((reacted.filter (placedAt parent)).map (liftBVars 0 owned)).map readT)))
      (Prenex.body ambientBlock (moved :: shrunk :: others.map readS)) := by
    refine .trans _ _ _ (restricts_congr (language := ambientCoreCalc) (block := ambientBlock) owned
      (body_perm_equivalent hereItemsMembers hereItemsPerm)) ?_
    refine .trans _ _ _ (restricts_body_middle (before := []) owned Members.nil keptMembers marker'ReadTyped) ?_
    exact body_congr (Members.cons (restricts_typed (language := ambientCoreCalc) (block := ambientBlock) owned
      marker'ReadTyped) keptMembers) (.cons movedSide (List.forall₂_same.mpr fun _ _ => .refl _))
  -- the source side: the stepped items, unpadded and flattened
  have paddedRelated : ∀ items : List Pattern, Members ambientCoreCalc ambientBlock free bound items →
      (∀ item ∈ items, isObjectPattern item = true) →
      List.Forall₂ (ProcEquiv ambientCoreCalc ambientBlock free bound) (items.map padA) items := by
    intro items itemsMembers itemsObjects
    refine List.forall₂_map_left_iff.mpr (List.forall₂_same.mpr fun item inItems => ?_)
    exact Relation.EqvGen.symm _ _ (padA_equivalent (size item + 1) (Nat.lt_succ_self _)
      (itemsMembers item inItems) (itemsObjects item inItems))
  have paddedMembers : ∀ items : List Pattern, Members ambientCoreCalc ambientBlock free bound items →
      (∀ item ∈ items, isObjectPattern item = true) → Members ambientCoreCalc ambientBlock free bound (items.map padA) :=
    fun items itemsMembers itemsObjects item inItems => by
      obtain ⟨original, inOriginal, rfl⟩ := List.mem_map.mp inItems
      exact padA_typed (itemsMembers original inOriginal) (itemsObjects original inOriginal)
  -- the moved ambient
  have erasedIs : ((atMover.map readM).map padA).eraseIdx k = ((atMover.eraseIdx k).map readM).map padA := by
    rw [List.eraseIdx_map, List.eraseIdx_map]
  have erasedPerm : ((atMover.eraseIdx k).map readM).Perm moverKept := by
    have perm := eraseIdx_perm_erase hk
    rw [capabilityAtK] at perm
    exact perm.map readM
  have erasedMembers : Members ambientCoreCalc ambientBlock free bound ((atMover.eraseIdx k).map readM) :=
    fun item inItems => moverKeptMembers item (erasedPerm.subset inItems)
  have erasedObjects : ∀ item ∈ (atMover.eraseIdx k).map readM, isObjectPattern item = true := fun item inItems => by
    obtain ⟨original, inErased, rfl⟩ := List.mem_map.mp inItems
    exact moverObjects _ (List.mem_map_of_mem (List.mem_of_mem_eraseIdx inErased))
  have innerMembers : Members ambientCoreCalc ambientBlock free bound
      (padA continuationRead :: ((atMover.eraseIdx k).map readM).map padA) :=
    Members.cons (padA_typed continuationTyped continuationObject) (paddedMembers _ erasedMembers erasedObjects)
  have innerSide : ProcEquiv ambientCoreCalc ambientBlock free bound
      (.collection .hashBag (padA continuationRead :: ((atMover.map readM).map padA).eraseIdx k) none)
      movedContent := by
    rw [erasedIs]
    refine .trans _ _ _ (bag_body_equivalent (language := ambientCoreCalc) (block := ambientBlock) innerMembers) ?_
    refine .trans _ _ _ (body_congr innerMembers (.cons (Relation.EqvGen.symm _ _
      (padA_equivalent (size continuationRead + 1) (Nat.lt_succ_self _) continuationTyped continuationObject))
      (paddedRelated _ erasedMembers erasedObjects))) ?_
    exact body_perm_equivalent (Members.cons continuationTyped erasedMembers) (erasedPerm.cons _)
  -- what is left of the ambient left
  have leftIs : ((atTarget.map readTS).map padA).eraseIdx i = ((atTarget.eraseIdx i).map readTS).map padA := by
    rw [List.eraseIdx_map, List.eraseIdx_map]
  have leftPerm : ((atTarget.eraseIdx i).map readTS).Perm targetKept := by
    have filtered := targetSplit.filter fun component => component != marker
    have keptAll : (atTarget.eraseIdx i).filter (fun component => component != marker) = atTarget.eraseIdx i :=
      List.filter_eq_self.mpr fun component inErased => by
        have different : component ≠ marker := fun same => markerOnceTarget (same ▸ inErased)
        simp [different]
    rw [List.filter_cons_of_neg (by simp), keptAll] at filtered
    exact (filtered.map readTS).symm
  have leftMembers : Members ambientCoreCalc ambientBlock free bound ((atTarget.eraseIdx i).map readTS) :=
    fun item inItems => targetKeptMembers item (leftPerm.subset inItems)
  have leftObjects : ∀ item ∈ (atTarget.eraseIdx i).map readTS, isObjectPattern item = true := fun item inItems => by
    obtain ⟨original, inErased, rfl⟩ := List.mem_map.mp inItems
    exact targetReadObjects _ (List.mem_map_of_mem (List.mem_of_mem_eraseIdx inErased))
  have leftPadded : Members ambientCoreCalc ambientBlock free bound (((atTarget.eraseIdx i).map readTS).map padA) :=
    paddedMembers _ leftMembers leftObjects
  have leftSide : ProcEquiv ambientCoreCalc ambientBlock free bound
      (.collection .hashBag (((atTarget.map readTS).map padA).eraseIdx i) none) (Prenex.body ambientBlock targetKept) := by
    rw [leftIs]
    refine .trans _ _ _ (bag_body_equivalent (language := ambientCoreCalc) (block := ambientBlock) leftPadded) ?_
    refine .trans _ _ _ (body_congr leftPadded (paddedRelated _ leftMembers leftObjects)) ?_
    exact body_perm_equivalent leftMembers leftPerm
  -- assembled
  have movedPaddedTyped : HasType ambientCoreCalc free bound
      (amb moverName (.collection .hashBag (padA continuationRead :: ((atMover.map readM).map padA).eraseIdx k) none))
      procType :=
    (Mettapedia.GSLT.LanguageDef.RestrictionBlocks.SortedEquiv.typed_iff (amb_fill moverNameTyped' innerSide)).mpr
      movedTyped
  have leftPaddedTyped : HasType ambientCoreCalc free bound
      (amb targetName (.collection .hashBag (((atTarget.map readTS).map padA).eraseIdx i) none)) procType :=
    (Mettapedia.GSLT.LanguageDef.RestrictionBlocks.SortedEquiv.typed_iff (amb_fill targetNameTyped' leftSide)).mpr
      shrunkTyped
  have othersPadded : Members ambientCoreCalc ambientBlock free bound (others.map (padA ∘ readS)) := by
    rw [← List.map_map]
    exact paddedMembers _ othersMembers othersObjects
  have flatMembers : Members ambientCoreCalc ambientBlock free bound
      ([] ++ [amb moverName (.collection .hashBag (padA continuationRead :: ((atMover.map readM).map padA).eraseIdx k)
        none), amb targetName (.collection .hashBag (((atTarget.map readTS).map padA).eraseIdx i) none)] ++
        others.map (padA ∘ readS)) :=
    Members.cons movedPaddedTyped (Members.cons leftPaddedTyped othersPadded)
  have sourceSide : ProcEquiv ambientCoreCalc ambientBlock free bound
      (.collection .hashBag (.collection .hashBag
        [amb moverName (.collection .hashBag (padA continuationRead :: ((atMover.map readM).map padA).eraseIdx k)
          none), amb targetName (.collection .hashBag (((atTarget.map readTS).map padA).eraseIdx i) none)] none ::
        others.map (padA ∘ readS)) none)
      (Prenex.body ambientBlock (moved :: shrunk :: others.map readS)) := by
    refine .trans _ _ _ (bag_flatten_ambient (pre := []) flatMembers) ?_
    refine body_congr flatMembers (.cons (amb_fill moverNameTyped' innerSide)
      (.cons (amb_fill targetNameTyped' leftSide) ?_))
    rw [← List.map_map]
    exact paddedRelated _ othersMembers othersObjects
  exact .trans _ _ _ sourceSide (Relation.EqvGen.symm _ _ targetSide)

end Mettapedia.Languages.ProcessCalculi.Ambient.Steps
