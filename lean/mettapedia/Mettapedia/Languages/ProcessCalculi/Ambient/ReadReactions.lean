import Mettapedia.Languages.ProcessCalculi.Ambient.LocatedReacts

/-!
# Reading a located reaction back as a step

A reaction of an unfolding of a process's root canonical block reads back as a step of the process's presentation:
the presentation holds, along the path of ambients from the root down to the place of the reaction, the ambients the
reaction's parts read as, and the step there leaves what the reacted block reads back as, the continuation's
restrictions moved down that path.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.Ambient.Steps

open Mettapedia.Languages.ProcessCalculi.Ambient.Comm (ambientCoreCalc)

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Substitution (liftBVars)
open Mettapedia.GSLT.LanguageDef.WellSorted (HasType FreeTypeContext isObjectPattern isObjectPatternList)
open Mettapedia.GSLT.LanguageDef.RestrictionBlocks (Prenex Members ProcEquiv rename)
open Mettapedia.Languages.ProcessCalculi.Ambient.Full (AmbNuRawStep ambientBlock)
open Mettapedia.Languages.ProcessCalculi.Ambient.Decoding (isVariable)

variable {free : FreeTypeContext}

/-! ## Steps under restrictions, padded bags -/

/-- **A step under restrictions** is a step. -/
theorem restricts_step : ∀ (count : Nat) {source target : Pattern}, AmbNuRawStep source target →
    AmbNuRawStep (Prenex.restricts ambientBlock count source) (Prenex.restricts ambientBlock count target)
  | 0, _, _, step => step
  | count + 1, _, _, step => by
      rw [Prenex.restricts_succ, Prenex.restricts_succ]
      exact .res none (restricts_step count step)

/-- **A padded reading of components** is the bag of its padded items, when it holds an item and a single item is
no bag. -/
theorem asBag_padA_body {items : List Pattern} (nonempty : items ≠ [])
    (single : ∀ item, items = [item] → ∀ elements, padA item ≠ .collection .hashBag elements none) :
    asBag (padA (Prenex.body ambientBlock items)) = .collection .hashBag (items.map padA) none := by
  match items, nonempty, single with
  | [item], _, single =>
      simp only [Prenex.body, List.map_cons, List.map_nil]
      unfold asBag
      split
      · rename_i elements same
        exact absurd same (single item rfl elements)
      · rfl
  | first :: second :: rest, _, _ =>
      simp only [Prenex.body, padA, padAList_eq_map]
      rfl

/-- The padded form of a variable is itself. -/
theorem padA_variable {pattern : Pattern} (isVar : isVariable pattern = true) : padA pattern = pattern := by
  cases pattern <;> simp_all [isVariable, padA]

/-- **A padded ambient of a variable name**: its content padded as a bag. -/
theorem padA_amb {name content : Pattern} (isVar : isVariable name = true) :
    padA (.apply "AAmb" [name, content]) = .apply "AAmb" [name, asBag (padA content)] := by
  simp [padA, padAList, padApply, padA_variable isVar]

/-- A padded ambient is no bag. -/
theorem padA_amb_ne_bag {name content : Pattern} (isVar : isVariable name = true) (elements : List Pattern) :
    padA (.apply "AAmb" [name, content]) ≠ .collection .hashBag elements none := by
  rw [padA_amb isVar]
  simp

/-- A padded capability is no bag. -/
theorem padA_apply_ne_bag {label : String} {arguments : List Pattern} (elements : List Pattern) :
    padA (.apply label arguments) ≠ .collection .hashBag elements none := by
  simp only [padA]
  unfold padApply
  split <;> (try split_ifs) <;> simp


/-! ## What a reading reaches -/

open Mettapedia.Languages.ProcessCalculi.Ambient.Decoding (Reaches placedAt placeAt childOf readPlaced readComponent
  readPlaced_congr)

/-- **A reached place's markers lead to reached places.** -/
theorem Reaches.child {components : List Pattern} {place target : Pattern} (reached : Reaches components place target) :
    ∀ {marker child : Pattern}, marker ∈ components → placedAt target marker = true → childOf marker = some child →
      Reaches components place child := by
  induction reached with
  | here => exact fun member isPlaced isChild => .down member isPlaced isChild .here
  | @down components place child' target marker' member' isPlaced' isChild' below recurse =>
      intro marker child member isPlaced isChild
      by_cases atPlace : placedAt place marker = true
      · exact .down member atPlace isChild .here
      · exact .down member' isPlaced' isChild'
          (recurse (List.mem_filter.mpr ⟨member, by simpa using atPlace⟩) isPlaced isChild)

/-- **Readings agree where the components agree at every reached place.** -/
theorem readPlaced_reach_congr (fuel : Nat) {first second : List Pattern} {place : Pattern}
    (same : ∀ at', Reaches first place at' → first.filter (placedAt at') = second.filter (placedAt at')) :
    readPlaced fuel place first = readPlaced fuel place second :=
  readPlaced_congr fuel (reach := Reaches first place) same
    (fun _ member _ reached isPlaced _ isChild => Reaches.child reached member isPlaced isChild) place .here

/-! ## What a reaction leaves, in place -/

/-- **The components a reaction leaves, in place**: the capability gone, one marker replaced by another. -/
def reactList (capability marker marker' : Pattern) (components : List Pattern) : List Pattern :=
  (components.erase capability).map fun component => if component = marker then marker' else component

/-- A reaction's components filtered are the filtered components reacted, when the filter keeps the marker exactly
when it keeps its replacement. -/
theorem reactList_filter {capability marker marker' : Pattern} {keep : Pattern → Bool}
    (keepSame : keep marker' = keep marker) (components : List Pattern) :
    (reactList capability marker marker' components).filter keep =
      reactList capability marker marker' (components.filter keep) := by
  unfold reactList
  rw [List.filter_map, List.erase_filter]
  congr 1
  apply List.filter_congr
  intro component _
  simp only [Function.comp]
  split_ifs with same
  · rw [same, keepSame]
  · rfl

/-- **Where the reaction touches nothing, its components are the original ones.** -/
theorem reactList_untouched {capability marker marker' : Pattern} {components : List Pattern}
    (noCapability : capability ∉ components) (noMarker : marker ∉ components) :
    reactList capability marker marker' components = components := by
  unfold reactList
  rw [List.erase_of_not_mem noCapability]
  conv_rhs => rw [← List.map_id components]
  refine List.map_congr_left fun component member => ?_
  have different : component ≠ marker := fun same => noMarker (same ▸ member)
  simp [different]

/-- At a place where neither the capability, the marker nor its replacement sits, the reaction's components there
are the original ones. -/
theorem reactList_at {capability marker marker' place : Pattern} {components : List Pattern}
    (capabilityApart : placedAt place capability = false) (markerApart : placedAt place marker = false)
    (marker'Apart : placedAt place marker' = false) :
    (reactList capability marker marker' components).filter (placedAt place) = components.filter (placedAt place) := by
  rw [reactList_filter (by rw [marker'Apart, markerApart])]
  refine reactList_untouched (fun member => ?_) (fun member => ?_)
  · simp [(List.mem_filter.mp member).2] at capabilityApart
  · simp [(List.mem_filter.mp member).2] at markerApart

/-- Elsewhere than a place where none of them sits, the reaction's components are the reaction of the components
elsewhere. -/
theorem reactList_elsewhere {capability marker marker' place : Pattern} {components : List Pattern}
    (markerApart : placedAt place marker = false) (marker'Apart : placedAt place marker' = false) :
    (reactList capability marker marker' components).filter (fun other => !placedAt place other) =
      reactList capability marker marker' (components.filter fun other => !placedAt place other) :=
  reactList_filter (by rw [marker'Apart, markerApart]) components


/-! ## Components the reaction does not touch -/

open Mettapedia.Languages.ProcessCalculi.Ambient.Decoding (readComponent_congr readComponent_lifted reaches_lifted
  placedAt_lift childOf_lift liftBVars_injective lift_ne_owned)

/-- A lifted list's components at a lifted place are the components there, lifted. -/
theorem filter_lift_at (owned : Nat) (place : Pattern) (components : List Pattern) :
    (components.map (liftBVars 0 owned)).filter (placedAt (liftBVars 0 owned place)) =
      (components.filter (placedAt place)).map (liftBVars 0 owned) := by
  rw [List.filter_map]
  congr 1
  exact List.filter_congr fun component _ => by simp [Function.comp, placedAt_lift]

/-- **A component whose ambients reach no place the reaction touches reads as before**, lifted past the continuation's
restrictions, beside the continuation's components. -/
theorem untouched_reads {react : List Pattern → List Pattern} {home : Pattern} {touched : List Pattern}
    {owned : Nat} {group : List Pattern}
    (groupPlaced : ∀ component ∈ group, ∀ at', placeAt component = some at' →
      at' = liftBVars 0 owned home ∨ ∃ index < owned, at' = .bvar index)
    (homeTouched : home ∈ touched)
    (reactAt : ∀ (list : List Pattern) (place : Pattern), place ∉ touched →
      (react list).filter (placedAt place) = list.filter (placedAt place))
    (fuel : Nat) (place component : Pattern) {rest : List Pattern}
    (apart : ∀ child, childOf component = some child → ∀ at' ∈ touched, ¬ Reaches rest child at') :
    readComponent fuel (liftBVars 0 owned place) (liftBVars 0 owned component)
        ((react rest).map (liftBVars 0 owned) ++ group) =
      liftBVars 0 owned (readComponent fuel place component rest) := by
  cases fuel with
  | zero => simp [readComponent, liftBVars, Mettapedia.Languages.ProcessCalculi.Ambient.Decoding.inaction]
  | succ fuel =>
      rw [← readComponent_lifted groupPlaced (fuel + 1) place component
        (fun child isChild reached => apart child isChild home homeTouched reached)]
      refine readComponent_congr fun child isChild => ?_
      rw [childOf_lift] at isChild
      cases found : childOf component with
      | none => rw [found] at isChild; cases isChild
      | some original =>
          rw [found, Option.map_some, Option.some.injEq] at isChild
          subst isChild
          refine (readPlaced_reach_congr fuel (first := rest.map (liftBVars 0 owned) ++ group) fun at' reached => ?_).symm
          rcases reaches_lifted groupPlaced reached with ⟨deep, rfl, deeper⟩ | toHome
          · have notTouched : deep ∉ touched := fun inTouched => apart original found deep inTouched deeper
            rw [List.filter_append, List.filter_append, filter_lift_at, filter_lift_at, reactAt rest deep notTouched]
          · exact absurd toHome (apart original found home homeTouched)


/-! ## Locations deepen below a place -/

/-- **Below a place, locations deepen**: a place reached from another, among the components of a nested block, is
one of the block's locations, deeper than the place when the place is one too. -/
theorem reaches_deeper {count : Nat} {components : List Pattern} {depth : Nat → Nat}
    (children : ∀ component ∈ components, ∀ child, childOf component = some child →
      ∃ index < count, child = .bvar index)
    (grows : ∀ component ∈ components, ∀ index child, index < count → child < count →
      placeAt component = some (.bvar index) → childOf component = some (.bvar child) → depth index < depth child) :
    ∀ {list : List Pattern} {place target : Pattern}, (∀ component ∈ list, component ∈ components) →
      Reaches list place target → place ≠ target →
      ∃ index < count, target = .bvar index ∧ ∀ start < count, place = .bvar start → depth start < depth index := by
  intro list place target within reached different
  induction reached with
  | here => exact absurd rfl different
  | @down list place child target marker member isPlaced isChild below recurse =>
      obtain ⟨childIndex, childBelow, rfl⟩ := children marker (within marker member) _ isChild
      have deeper : ∀ start < count, place = .bvar start → depth start < depth childIndex := by
        intro start startBelow rfl
        exact grows marker (within marker member) start childIndex startBelow childBelow
          (by simpa [placedAt] using isPlaced) isChild
      by_cases atTarget : Pattern.bvar childIndex = target
      · subst atTarget
        exact ⟨childIndex, childBelow, rfl, deeper⟩
      · obtain ⟨index, indexBelow, rfl, further⟩ :=
          recurse (fun component inFiltered => within component (List.mem_filter.mp inFiltered).1) atTarget
        exact ⟨index, indexBelow, rfl, fun start startBelow same =>
          (deeper start startBelow same).trans (further childIndex childBelow rfl)⟩

/-- **No place is above a place below it**: two different places do not reach each other. -/
theorem reaches_antisymm {count : Nat} {components : List Pattern} {depth : Nat → Nat}
    (children : ∀ component ∈ components, ∀ child, childOf component = some child →
      ∃ index < count, child = .bvar index)
    (grows : ∀ component ∈ components, ∀ index child, index < count → child < count →
      placeAt component = some (.bvar index) → childOf component = some (.bvar child) → depth index < depth child)
    {first second : List Pattern} {upper lower : Pattern}
    (firstWithin : ∀ component ∈ first, component ∈ components)
    (secondWithin : ∀ component ∈ second, component ∈ components)
    (down : Reaches first upper lower) (up : Reaches second lower upper) : upper = lower := by
  by_contra different
  obtain ⟨lowerIndex, lowerBelow, lowerIs, upperDeeper⟩ := reaches_deeper children grows firstWithin down different
  obtain ⟨upperIndex, upperBelow, upperIs, lowerDeeper⟩ :=
    reaches_deeper children grows secondWithin up (Ne.symm different)
  have one := upperDeeper upperIndex upperBelow upperIs
  have two := lowerDeeper lowerIndex lowerBelow lowerIs
  omega


/-! ## Reading an ambient on the path -/

open Mettapedia.Languages.ProcessCalculi.Ambient.Decoding (markers wrapContent readPlaced_succ)

/-- **An ambient's marker reads as the ambient** around its location's reading. -/
theorem readComponent_amb (fuel : Nat) (place : Pattern) {parent child name : Pattern}
    (isVar : isVariable name = true) (elsewhere : List Pattern) :
    readComponent (fuel + 1) place (.apply "LAmb" [parent, child, name]) elsewhere =
      .apply "AAmb" [name, Prenex.body ambientBlock (readPlaced fuel child elsewhere)] := by
  simp [readComponent, markers, wrapContent, isVar]

/-- **A component other than an opened marker reads as an application.** -/
theorem readComponent_isApply (fuel : Nat) (place : Pattern) {component : Pattern}
    (notOpened : ∀ first second third, component ≠ .apply "LOpened" [first, second, third])
    (elsewhere : List Pattern) : ∃ label arguments, readComponent fuel place component elsewhere = .apply label arguments := by
  cases fuel with
  | zero => exact ⟨_, _, rfl⟩
  | succ fuel =>
      cases component with
      | apply label arguments =>
          match arguments, notOpened with
          | [first, second, third], notOpened =>
              simp only [readComponent]
              split_ifs with isMarker isVar
              · have isAmb : label = "LAmb" := by
                  simp only [markers, List.mem_cons, List.not_mem_nil, or_false] at isMarker
                  rcases isMarker with rfl | rfl
                  · rfl
                  · exact absurd rfl (notOpened first second third)
                subst isAmb
                exact ⟨"AAmb", _, Mettapedia.Languages.ProcessCalculi.Ambient.Decoding.wrapContent_amb _ _⟩
              all_goals exact ⟨_, _, rfl⟩
          | [], _ => exact ⟨_, _, rfl⟩
          | [argument], _ =>
              simp only [readComponent]
              split_ifs <;> exact ⟨_, _, rfl⟩
          | [_, second], _ =>
              simp only [readComponent]
              split_ifs
              · cases second <;> exact ⟨_, _, rfl⟩
              all_goals exact ⟨_, _, rfl⟩
          | _ :: _ :: _ :: _ :: _, _ => exact ⟨_, _, rfl⟩
      | _ => exact ⟨_, _, rfl⟩

/-- **A place some component sits at reads as something.** -/
theorem readPlaced_ne_nil {fuel : Nat} {place : Pattern} {components : List Pattern} {component : Pattern}
    (member : component ∈ components) (isPlaced : placedAt place component = true) :
    readPlaced (fuel + 1) place components ≠ [] := by
  rw [readPlaced_succ]
  intro empty
  rw [List.map_eq_nil_iff, List.filter_eq_nil_iff] at empty
  exact absurd isPlaced (by simpa using empty component member)

/-- **An ambient read and padded**: the ambient around the bag of its location's padded items, when a component that
is no opened marker sits at the location. -/
theorem padded_amb (fuel : Nat) (place : Pattern) {parent child name : Pattern} (isVar : isVariable name = true)
    {elsewhere : List Pattern} {component : Pattern} (member : component ∈ elsewhere)
    (isPlaced : placedAt child component = true)
    (notOpened : ∀ first second third, component ≠ .apply "LOpened" [first, second, third]) :
    padA (readComponent (fuel + 2) place (.apply "LAmb" [parent, child, name]) elsewhere) =
      .apply "AAmb" [name, .collection .hashBag ((readPlaced (fuel + 1) child elsewhere).map padA) none] := by
  rw [readComponent_amb _ _ isVar, padA_amb isVar,
    asBag_padA_body (readPlaced_ne_nil member isPlaced) fun item single elements => ?_]
  rw [readPlaced_succ, List.map_eq_singleton_iff] at single
  obtain ⟨original, filteredIs, rfl⟩ := single
  have same : component = original := by
    have inFiltered : component ∈ elsewhere.filter (placedAt child) := List.mem_filter.mpr ⟨member, isPlaced⟩
    rw [filteredIs] at inFiltered
    exact List.mem_singleton.mp inFiltered
  subst same
  obtain ⟨label, arguments, isApplication⟩ := readComponent_isApply fuel child notOpened _
  rw [isApplication]
  exact padA_apply_ne_bag elements

/-- **An opened marker reads as its location's reading**, in place. -/
theorem readComponent_opened (fuel : Nat) (place : Pattern) {parent child name : Pattern}
    (isVar : isVariable name = true) (elsewhere : List Pattern) :
    readComponent (fuel + 1) place (.apply "LOpened" [parent, child, name]) elsewhere =
      Prenex.body ambientBlock (readPlaced fuel child elsewhere) := by
  simp [readComponent, markers, wrapContent, isVar]

/-! ## Steps of bags of one -/

/-- **A bag of one process steps only inside it.** -/
theorem bag_single_step {item result : Pattern} {tail : Option String}
    (step : AmbNuRawStep (.collection .hashBag [item] tail) result) :
    ∃ inner, AmbNuRawStep item inner ∧ result = .collection .hashBag [inner] none := by
  cases step with
  | «open» i hi j hj name process content capability boundary =>
      have zero : i = 0 := by simpa using hi
      subst zero
      simp at hj
  | enter i hi j hj name target process host k hk mover capability destination =>
      have zero : i = 0 := by simpa using hi
      subst zero
      simp at hj
  | par i hi inner =>
      have zero : i = 0 := by simpa using hi
      subst zero
      exact ⟨_, inner, rfl⟩

/-- **The padded reading of items steps as the bag of their padded forms does**, up to a bag of one around the
result, for any step relation in which a bag of one steps only inside it. -/
theorem body_step_of {Step : Pattern → Pattern → Prop}
    (single : ∀ {item result : Pattern} {tail : Option String}, Step (.collection .hashBag [item] tail) result →
      ∃ inner, Step item inner ∧ result = .collection .hashBag [inner] none)
    {items : List Pattern} {result : Pattern} (nonempty : items ≠ [])
    (step : Step (.collection .hashBag (items.map padA) none) result) :
    ∃ result', Step (padA (Prenex.body ambientBlock items)) result' ∧
      (result' = result ∨ result = .collection .hashBag [result'] none) := by
  match items, nonempty, step with
  | [item], _, step =>
      obtain ⟨inner, innerStep, rfl⟩ := single step
      exact ⟨inner, innerStep, .inr rfl⟩
  | first :: second :: rest, _, step =>
      have shape : padA (Prenex.body ambientBlock (first :: second :: rest)) =
          .collection .hashBag ((first :: second :: rest).map padA) none := by
        simp only [Prenex.body, padA, padAList_eq_map]
      rw [shape]
      exact ⟨result, step, .inl rfl⟩

/-- **An ambient's padded content steps as the bag of its padded items does**, up to a bag of one around the
result, for any step relation in which a bag of one steps only inside it. -/
theorem asBag_step_of {Step : Pattern → Pattern → Prop}
    (single : ∀ {item result : Pattern} {tail : Option String}, Step (.collection .hashBag [item] tail) result →
      ∃ inner, Step item inner ∧ result = .collection .hashBag [inner] none)
    {items : List Pattern} {result : Pattern} (nonempty : items ≠ [])
    (step : Step (.collection .hashBag (items.map padA) none) result) :
    ∃ result', Step (asBag (padA (Prenex.body ambientBlock items))) result' ∧
      (result' = result ∨ result = .collection .hashBag [result'] none) := by
  match items, nonempty, step with
  | [item], _, step =>
      simp only [Prenex.body]
      unfold asBag
      split
      · rename_i elements isBag
        obtain ⟨inner, innerStep, rfl⟩ := single step
        exact ⟨inner, isBag ▸ innerStep, .inr rfl⟩
      · exact ⟨result, step, .inl rfl⟩
  | first :: second :: rest, _, step =>
      have shape : padA (Prenex.body ambientBlock (first :: second :: rest)) =
          .collection .hashBag ((first :: second :: rest).map padA) none := by
        simp only [Prenex.body, padA, padAList_eq_map]
      rw [shape]
      exact ⟨result, step, .inl rfl⟩

/-- **The padded reading of items steps as the bag of their padded forms does**, up to a bag of one around the
result. -/
theorem body_step {items : List Pattern} {result : Pattern} (nonempty : items ≠ [])
    (step : AmbNuRawStep (.collection .hashBag (items.map padA) none) result) :
    ∃ result', AmbNuRawStep (padA (Prenex.body ambientBlock items)) result' ∧
      (result' = result ∨ result = .collection .hashBag [result'] none) := by
  match items, nonempty, step with
  | [item], _, step =>
      obtain ⟨inner, innerStep, rfl⟩ := bag_single_step step
      exact ⟨inner, innerStep, .inr rfl⟩
  | first :: second :: rest, _, step =>
      have shape : padA (Prenex.body ambientBlock (first :: second :: rest)) =
          .collection .hashBag ((first :: second :: rest).map padA) none := by
        simp only [Prenex.body, padA, padAList_eq_map]
      rw [shape]
      exact ⟨result, step, .inl rfl⟩

/-- **An ambient's padded content steps as the bag of its padded items does**, up to a bag of one around the
result. -/
theorem asBag_step {items : List Pattern} {result : Pattern} (nonempty : items ≠ [])
    (step : AmbNuRawStep (.collection .hashBag (items.map padA) none) result) :
    ∃ result', AmbNuRawStep (asBag (padA (Prenex.body ambientBlock items))) result' ∧
      (result' = result ∨ result = .collection .hashBag [result'] none) := by
  match items, nonempty, step with
  | [item], _, step =>
      simp only [Prenex.body]
      unfold asBag
      split
      · rename_i elements isBag
        obtain ⟨inner, innerStep, rfl⟩ := bag_single_step step
        exact ⟨inner, isBag ▸ innerStep, .inr rfl⟩
      · exact ⟨result, step, .inl rfl⟩
  | first :: second :: rest, _, step =>
      have shape : padA (Prenex.body ambientBlock (first :: second :: rest)) =
          .collection .hashBag ((first :: second :: rest).map padA) none := by
        simp only [Prenex.body, padA, padAList_eq_map]
      rw [shape]
      exact ⟨result, step, .inl rfl⟩


/-- What a reaction leaves comes from the components or is the marker's replacement. -/
theorem mem_reactList {capability marker marker' component : Pattern} {components : List Pattern}
    (member : component ∈ reactList capability marker marker' components) : component ∈ components ∨ component = marker' := by
  obtain ⟨original, inErased, rfl⟩ := List.mem_map.mp member
  split_ifs
  · exact .inr rfl
  · exact .inl (List.mem_of_mem_erase inErased)

/-- A lifted list's components elsewhere than a lifted place are the components elsewhere, lifted. -/
theorem filter_lift_elsewhere (owned : Nat) (place : Pattern) (components : List Pattern) :
    (components.map (liftBVars 0 owned)).filter (fun other => !placedAt (liftBVars 0 owned place) other) =
      (components.filter fun other => !placedAt place other).map (liftBVars 0 owned) := by
  rw [List.filter_map]
  congr 1
  exact List.filter_congr fun component _ => by simp [Function.comp, placedAt_lift]

/-! ## Down the path to the reaction -/

open Mettapedia.GSLT.LanguageDef.RestrictionBlocks (sizeList size body_congr body_perm_equivalent bag_body_equivalent
  restricts_typed body_typed)
open Mettapedia.Languages.ProcessCalculi.Ambient.Located (locatedCalc locatedBlock)
open Mettapedia.Languages.ProcessCalculi.Ambient.Encoding (nameType procType)
open Mettapedia.Languages.ProcessCalculi.Ambient.Full (amb_fill amb_typed)
open Mettapedia.Languages.ProcessCalculi.Ambient.Decoding (restricts_body_middle restricts_amb_equivalent decode_typed
  decode_object reaches_unique unkept_beside eq_of_filter_length_le_one size_add_elsewhere variable_typed
  placeAt_ofMarker triple_inv forall₂_middle)

/-- A place a reach starts from holds a component, when it holds one where the reach ends there. -/
theorem Reaches.occupied {components : List Pattern} {place target : Pattern} (reached : Reaches components place target)
    (atTarget : place = target → ∃ component ∈ components, placedAt place component = true) :
    ∃ component ∈ components, placedAt place component = true := by
  cases reached with
  | here => exact atTarget rfl
  | down member isPlaced _ _ => exact ⟨_, member, isPlaced⟩

/-- **A reaction below a place reads, from the place, as a step**: the bag of the padded items read there steps to
what the reacted components read as there, under the continuation's restrictions, the step taken in the ambient on
the path down to the reaction, or in place where the path passes an opened ambient. Any step relation with steps in a
bag and inside an ambient, where a bag of one steps only inside it, and any reaction that leaves the components where
it touches nothing as they are, serve. -/
theorem path_step_of {bound : List TypeExpr} {count : Nat} {components : List Pattern} {depth : Nat → Nat}
    (children : ∀ component ∈ components, ∀ child, childOf component = some child →
      ∃ index < count, child = .bvar index)
    (grows : ∀ component ∈ components, ∀ index child, index < count → child < count →
      placeAt component = some (.bvar index) → childOf component = some (.bvar child) → depth index < depth child)
    (unique : ∀ child, (components.filter fun component => childOf component == some child).length ≤ 1)
    (markersOf : ∀ component ∈ components, ∀ child, childOf component = some child →
      ∃ label parent name, label ∈ markers ∧ component = .apply label [parent, child, name] ∧
        isVariable name = true)
    (typed : Members locatedCalc locatedBlock free bound components)
    {redexPlace home : Pattern} {touched : List Pattern} {owned : Nat}
    {group : List Pattern}
    (groupPlaced : ∀ component ∈ group, ∀ at', placeAt component = some at' →
      at' = liftBVars 0 owned home ∨ ∃ index < owned, at' = .bvar index)
    (groupTyped : Members locatedCalc locatedBlock free (List.replicate owned nameType ++ bound) group)
    (homeTouched : home ∈ touched)
    {Step : Pattern → Pattern → Prop}
    (parStep : ∀ {elements : List Pattern} (i : Nat) (hi : i < elements.length) {target : Pattern},
      Step elements[i] target →
        Step (.collection .hashBag elements none) (.collection .hashBag (target :: elements.eraseIdx i) none))
    (ambientStep : ∀ (name : Pattern) {content target : Pattern}, Step content target →
      Step (.apply "AAmb" [name, content]) (.apply "AAmb" [name, target]))
    (single : ∀ {item result : Pattern} {tail : Option String}, Step (.collection .hashBag [item] tail) result →
      ∃ inner, Step item inner ∧ result = .collection .hashBag [inner] none)
    {react : List Pattern → List Pattern}
    (reactAt : ∀ (list : List Pattern) (place : Pattern), place ∉ touched →
      (react list).filter (placedAt place) = list.filter (placedAt place))
    (reactElsewhere : ∀ (list : List Pattern) (place : Pattern), place ∉ touched →
      (react list).filter (fun other => !placedAt place other) =
        react (list.filter fun other => !placedAt place other))
    (reactTyped : ∀ list : List Pattern, Members locatedCalc locatedBlock free bound list →
      Members locatedCalc locatedBlock free bound (react list))
    {Holds : List Pattern → Prop}
    (holdsKeep : ∀ list place, Holds list → place ∉ touched → Holds (list.filter fun other => !placedAt place other))
    (holdsTouched : ∀ list, Holds list → ∀ start, Reaches list start redexPlace → ∀ at' ∈ touched,
      Reaches list start at')
    (holdsHere : ∀ list, Holds list → ∃ component ∈ list, placedAt redexPlace component = true)
    {extra : Nat}
    (localStep : ∀ list, Holds list → list.Sublist components → ∀ fuel, 3 * sizeList list + extra ≤ fuel →
      ∃ result, Step (.collection .hashBag ((readPlaced fuel redexPlace list).map padA) none) result ∧
        ProcEquiv ambientCoreCalc ambientBlock free bound result (Prenex.restricts ambientBlock owned
          (Prenex.body ambientBlock (readPlaced fuel (liftBVars 0 owned redexPlace)
            ((react list).map (liftBVars 0 owned) ++ group))))) :
    ∀ {list : List Pattern} {place target : Pattern}, Reaches list place target → target = redexPlace →
      list.Sublist components → Holds list → ∀ fuel, 3 * sizeList list + extra + 3 ≤ fuel →
      ∃ result, Step (.collection .hashBag ((readPlaced fuel place list).map padA) none) result ∧
        ProcEquiv ambientCoreCalc ambientBlock free bound result (Prenex.restricts ambientBlock owned
          (Prenex.body ambientBlock (readPlaced fuel (liftBVars 0 owned place)
            ((react list).map (liftBVars 0 owned) ++ group)))) := by
  intro list place target reached
  induction reached with
  | here =>
      intro targetIs sub holds fuel enough
      subst targetIs
      exact localStep _ holds sub fuel (by omega)
  | @down list place child target pathMarker member isPlaced isChild below recurse =>
      intro targetIs sub holds fuel enough
      subst target
      by_cases atRedex : place = redexPlace
      · subst atRedex
        exact localStep _ holds sub fuel (by omega)
      have within : ∀ component ∈ list, component ∈ components := fun component inList => sub.subset inList
      have notTouched : place ∉ touched := fun inTouched => atRedex (reaches_antisymm children grows within within
        (.down member isPlaced isChild below) (holdsTouched list holds _ .here place inTouched))
      -- the marker on the path, at the place
      obtain ⟨label, parent, name, isMarker, rfl, nameVar⟩ := markersOf pathMarker (within _ member) child isChild
      have parentIs : parent = place := by
        simpa [placedAt, placeAt_ofMarker isMarker] using isPlaced
      subst parentIs
      obtain ⟨g, rfl⟩ : ∃ g, fuel = g + 3 := ⟨fuel - 3, by omega⟩
      set elsewhere := list.filter fun other => !placedAt parent other with elsewhereIs
      have subElsewhere : elsewhere.Sublist components := List.filter_sublist.trans sub
      have holdsElsewhere := holdsKeep list parent holds notTouched
      have markerHere : Pattern.apply label [parent, child, name] ∈ list.filter (placedAt parent) :=
        List.mem_filter.mpr ⟨member, isPlaced⟩
      have sizeBound : 3 * sizeList elsewhere + extra + 3 ≤ g + 1 := by
        have split : size (Pattern.apply label [parent, child, name]) + sizeList elsewhere ≤ sizeList list :=
          size_add_elsewhere markerHere
        have markerSize : 4 ≤ size (Pattern.apply label [parent, child, name]) := by
          simp only [size, sizeList]
          have := Mettapedia.Languages.ProcessCalculi.Ambient.Decoding.size_pos parent
          have := Mettapedia.Languages.ProcessCalculi.Ambient.Decoding.size_pos child
          have := Mettapedia.Languages.ProcessCalculi.Ambient.Decoding.size_pos name
          omega
        omega
      obtain ⟨inner, innerStep, innerEquiv⟩ := recurse rfl subElsewhere holdsElsewhere (g + 1) sizeBound
      -- the components at the place, the marker among them
      obtain ⟨before, after, splitIs⟩ := List.append_of_mem markerHere
      have uniqueHere : ∀ child', (list.filter fun component => childOf component == some child').length ≤ 1 :=
        fun child' => le_trans (sub.filter _).length_le (unique child')
      -- the other components there reach nothing the reaction touches
      have apart : ∀ other ∈ before ++ after, ∀ child', childOf other = some child' → ∀ at' ∈ touched,
          ¬ Reaches elsewhere child' at' := by
        intro other otherIn child' isChild' at' inTouched reached'
        have otherHere : other ∈ list.filter (placedAt parent) := by
          rw [splitIs]
          rcases List.mem_append.mp otherIn with inBefore | inAfter
          · exact List.mem_append_left _ inBefore
          · exact List.mem_append_right _ (List.mem_cons_of_mem _ inAfter)
        obtain ⟨steps, reachedSteps⟩ :=
          Mettapedia.Languages.ProcessCalculi.Ambient.Decoding.Reaches.steps
            (holdsTouched elsewhere holdsElsewhere child below at' inTouched)
        have patternUnique : ∀ first ∈ list, ∀ second ∈ list, ∀ child'', childOf first = some child'' →
            childOf second = some child'' → first = second :=
          fun first firstIn second secondIn child'' firstChild secondChild =>
            eq_of_filter_length_le_one (uniqueHere child'') firstIn secondIn (by simp [firstChild])
              (by simp [secondChild])
        have sameChild := reaches_unique patternUnique (fun component inList => inList) steps reachedSteps reached'
          ⟨_, member, isPlaced, isChild⟩ ⟨other, (List.mem_filter.mp otherHere).1, (List.mem_filter.mp otherHere).2,
            isChild'⟩
        subst sameChild
        have subHere : (before ++ Pattern.apply label [parent, child, name] :: after).Sublist list := by
          rw [← splitIs]
          exact List.filter_sublist
        have unkept := unkept_beside (keep := fun component => childOf component == some child)
          subHere (uniqueHere child) (by simp [childOf, isMarker]) other otherIn
        simp [isChild'] at unkept
      -- the source: the items at the place, the marker's among them
      have sourceIs : readPlaced (g + 3) parent list =
          before.map (fun other => readComponent (g + 2) parent other elsewhere) ++
            readComponent (g + 2) parent (.apply label [parent, child, name]) elsewhere ::
              after.map (fun other => readComponent (g + 2) parent other elsewhere) := by
        rw [readPlaced_succ, splitIs, List.map_append, List.map_cons]
      obtain ⟨occupant, occupantIn, occupantPlaced⟩ := Reaches.occupied below fun same => by
        rw [same]
        exact holdsHere elsewhere holdsElsewhere
      have nonempty : readPlaced (g + 1) child elsewhere ≠ [] := readPlaced_ne_nil occupantIn occupantPlaced
      set beforeRead := before.map (fun other => readComponent (g + 2) parent other elsewhere) with beforeReadIs
      set afterRead := after.map (fun other => readComponent (g + 2) parent other elsewhere) with afterReadIs
      -- the target: the same items lifted, the marker's reading among them
      have groupApart : ∀ component ∈ group, placedAt (liftBVars 0 owned parent) component = false := by
        intro component inGroup
        cases sits : placeAt component with
        | none => simp [placedAt, sits]
        | some at' =>
            have different : at' ≠ liftBVars 0 owned parent := by
              rcases groupPlaced component inGroup at' sits with atHome | ⟨index, belowOwned, isOwned⟩
              · rw [atHome]
                intro same
                exact notTouched (liftBVars_injective owned same ▸ homeTouched)
              · rw [isOwned]
                exact fun same => lift_ne_owned belowOwned same.symm
            simp [placedAt, sits, different]
      have groupNone : group.filter (placedAt (liftBVars 0 owned parent)) = [] :=
        List.filter_eq_nil_iff.mpr fun component inGroup isPlaced' => by
          simp [groupApart component inGroup] at isPlaced'
      have groupAll : group.filter (fun other => !placedAt (liftBVars 0 owned parent) other) = group :=
        List.filter_eq_self.mpr fun component inGroup => by simp [groupApart component inGroup]
      have hereReacted : ((react list).map (liftBVars 0 owned) ++ group).filter
          (placedAt (liftBVars 0 owned parent)) = (list.filter (placedAt parent)).map (liftBVars 0 owned) := by
        rw [List.filter_append, filter_lift_at, reactAt list parent notTouched, groupNone, List.append_nil]
      have elsewhereReacted : ((react list).map (liftBVars 0 owned) ++ group).filter
          (fun other => !placedAt (liftBVars 0 owned parent) other) =
          (react elsewhere).map (liftBVars 0 owned) ++ group := by
        rw [List.filter_append, filter_lift_elsewhere, reactElsewhere list parent notTouched, groupAll]
      have liftedMarker : liftBVars 0 owned (Pattern.apply label [parent, child, name]) =
          .apply label [liftBVars 0 owned parent, liftBVars 0 owned child, liftBVars 0 owned name] := by
        simp [liftBVars, Mettapedia.OSLF.MeTTaIL.Substitution.liftBVarsList_eq_map]
      set reached' := (react elsewhere).map (liftBVars 0 owned) ++ group
        with reached'Is
      set middle := readComponent (g + 2) (liftBVars 0 owned parent)
        (.apply label [liftBVars 0 owned parent, liftBVars 0 owned child, liftBVars 0 owned name]) reached'
        with middleIs
      have targetIs : readPlaced (g + 3) (liftBVars 0 owned parent)
          ((react list).map (liftBVars 0 owned) ++ group) =
          beforeRead.map (liftBVars 0 owned) ++ middle :: afterRead.map (liftBVars 0 owned) := by
        rw [readPlaced_succ, hereReacted, elsewhereReacted, splitIs, List.map_map, List.map_append, List.map_cons,
          beforeReadIs, afterReadIs, List.map_map, List.map_map]
        refine congrArg₂ (· ++ ·) ?_ (congrArg₂ List.cons ?_ ?_)
        · refine List.map_congr_left fun other otherIn => ?_
          exact untouched_reads groupPlaced homeTouched reactAt _ _ _
            (apart other (List.mem_append_left _ otherIn))
        · simp only [Function.comp]
          rw [liftedMarker]
        · refine List.map_congr_left fun other otherIn => ?_
          exact untouched_reads groupPlaced homeTouched reactAt _ _ _
            (apart other (List.mem_append_right _ otherIn))
      rw [targetIs]
      -- typing
      have sourceMembers : Members ambientCoreCalc ambientBlock free bound (readPlaced (g + 3) parent list) :=
        (decode_typed (g + 3)).2.1 parent list (fun component inList => typed component (within component inList))
      have sourceObjects : ∀ item ∈ readPlaced (g + 3) parent list, isObjectPattern item = true :=
        (decode_object (g + 3)).2.1 parent list
      have beforeMembers : Members ambientCoreCalc ambientBlock free bound beforeRead := fun item inBefore =>
        sourceMembers item (by rw [sourceIs]; exact List.mem_append_left _ inBefore)
      have afterMembers : Members ambientCoreCalc ambientBlock free bound afterRead := fun item inAfter =>
        sourceMembers item (by rw [sourceIs]; exact List.mem_append_right _ (List.mem_cons_of_mem _ inAfter))
      have reactedMembers : Members locatedCalc locatedBlock free bound (react elsewhere) :=
        reactTyped elsewhere fun component inElsewhere => typed component (subElsewhere.subset inElsewhere)
      have reached'Members : Members locatedCalc locatedBlock free (List.replicate owned nameType ++ bound)
          reached' := by
        have lifted := Mettapedia.GSLT.LanguageDef.RestrictionBlocks.Members.lift (language := locatedCalc)
          (block := locatedBlock) (List.replicate owned nameType) reactedMembers
        rw [List.length_replicate] at lifted
        exact lifted.append groupTyped
      have bodyTyped : HasType ambientCoreCalc free (List.replicate owned nameType ++ bound)
          (Prenex.body ambientBlock (readPlaced (g + 1) (liftBVars 0 owned child) reached')) procType :=
        body_typed ((decode_typed (g + 1)).2.1 _ _ reached'Members)
      have liftedNameVar : isVariable (liftBVars 0 owned name) = true := by
        rw [Mettapedia.Languages.ProcessCalculi.Ambient.Decoding.isVariable_lift]
        exact nameVar
      have innerTyped : HasType ambientCoreCalc free bound inner procType :=
        (Mettapedia.GSLT.LanguageDef.RestrictionBlocks.SortedEquiv.typed_iff (Relation.EqvGen.symm _ _ innerEquiv)).mp
          (restricts_typed (language := ambientCoreCalc) (block := ambientBlock) owned bodyTyped)
      have fromRelated : ∀ {stepped : Pattern},
          (stepped = inner ∨ inner = .collection .hashBag [stepped] none) →
          HasType ambientCoreCalc free bound stepped procType ∧
            ProcEquiv ambientCoreCalc ambientBlock free bound stepped inner := by
        intro stepped related
        rcases related with rfl | isBag
        · exact ⟨innerTyped, .refl _⟩
        · have steppedTyped : HasType ambientCoreCalc free bound stepped procType :=
            Mettapedia.GSLT.LanguageDef.RestrictionBlocks.members_of_bag (language := ambientCoreCalc)
              (block := ambientBlock) (isBag ▸ innerTyped) stepped (List.mem_singleton_self _)
          refine ⟨steppedTyped, ?_⟩
          rw [isBag]
          exact Relation.EqvGen.symm _ _ (bag_body_equivalent (language := ambientCoreCalc) (block := ambientBlock)
            (Members.cons steppedTyped Members.nil))
      -- the marker's item steps, against the marker's reading in the target
      obtain ⟨stepped, itemStep, steppedTyped, middleTyped, middleRelated⟩ : ∃ stepped,
          Step (padA (readComponent (g + 2) parent (.apply label [parent, child, name]) elsewhere)) stepped ∧
          HasType ambientCoreCalc free bound stepped procType ∧
          HasType ambientCoreCalc free (List.replicate owned nameType ++ bound) middle procType ∧
          ProcEquiv ambientCoreCalc ambientBlock free bound (Prenex.restricts ambientBlock owned middle) stepped := by
        have kinds : label = "LAmb" ∨ label = "LOpened" := by simpa [markers] using isMarker
        rcases kinds with rfl | rfl
        · -- an ambient on the path: the step inside it
          have nameTyped : HasType ambientCoreCalc free bound name nameType := by
            rcases triple_inv (typed _ (within _ member)) with ⟨-, -, third⟩ | ⟨listed, -, -⟩ | ⟨isCap, -, -⟩
            · exact variable_typed third nameVar
            · simp at listed
            · simp at isCap
          have liftedNameTyped : HasType ambientCoreCalc free (List.replicate owned nameType ++ bound)
              (liftBVars 0 owned name) nameType := by
            simpa using Mettapedia.GSLT.LanguageDef.RestrictionBlocks.lift_typed (language := ambientCoreCalc)
              (inner := []) (inserted := List.replicate owned nameType) (outer := bound) nameTyped
          obtain ⟨inner', innerStep', related⟩ := asBag_step_of single nonempty innerStep
          obtain ⟨inner'Typed, inner'Equiv⟩ := fromRelated (related.imp id id)
          have middleIs' : middle = .apply "AAmb" [liftBVars 0 owned name,
              Prenex.body ambientBlock (readPlaced (g + 1) (liftBVars 0 owned child) reached')] := by
            rw [middleIs, readComponent_amb _ _ liftedNameVar]
          refine ⟨.apply "AAmb" [name, inner'], ?_, amb_typed nameTyped inner'Typed, ?_, ?_⟩
          · rw [readComponent_amb _ _ nameVar, padA_amb nameVar]
            exact ambientStep name innerStep'
          · rw [middleIs']
            exact amb_typed liftedNameTyped bodyTyped
          · rw [middleIs']
            exact .trans _ _ _ (restricts_amb_equivalent owned nameTyped bodyTyped)
              (amb_fill nameTyped (.trans _ _ _ (Relation.EqvGen.symm _ _ innerEquiv)
                (Relation.EqvGen.symm _ _ inner'Equiv)))
        · -- an opened ambient on the path: the step in place
          obtain ⟨inner', innerStep', related⟩ := body_step_of single nonempty innerStep
          obtain ⟨inner'Typed, inner'Equiv⟩ := fromRelated (related.imp id id)
          have middleIs' : middle =
              Prenex.body ambientBlock (readPlaced (g + 1) (liftBVars 0 owned child) reached') := by
            rw [middleIs, readComponent_opened _ _ liftedNameVar]
          refine ⟨inner', ?_, inner'Typed, ?_, ?_⟩
          · rw [readComponent_opened _ _ nameVar]
            exact innerStep'
          · rw [middleIs']
            exact bodyTyped
          · rw [middleIs']
            exact .trans _ _ _ (Relation.EqvGen.symm _ _ innerEquiv) (Relation.EqvGen.symm _ _ inner'Equiv)
      -- the source's step: the marker's item steps beside the others
      have itemsSplit : (readPlaced (g + 3) parent list).map padA = beforeRead.map padA ++
          padA (readComponent (g + 2) parent (.apply label [parent, child, name]) elsewhere) ::
            afterRead.map padA := by
        rw [sourceIs, List.map_append, List.map_cons]
      have positionBelow : (beforeRead.map padA).length < ((readPlaced (g + 3) parent list).map padA).length := by
        rw [itemsSplit]
        simp
      have itemAt : ((readPlaced (g + 3) parent list).map padA)[(beforeRead.map padA).length] =
          padA (readComponent (g + 2) parent (.apply label [parent, child, name]) elsewhere) := by
        simp only [itemsSplit, List.getElem_append_right (Nat.le_refl _), Nat.sub_self, List.getElem_cons_zero]
      have step : Step (.collection .hashBag ((readPlaced (g + 3) parent list).map padA) none)
          (.collection .hashBag (stepped ::
            ((readPlaced (g + 3) parent list).map padA).eraseIdx (beforeRead.map padA).length) none) :=
        parStep _ positionBelow (by rw [itemAt]; exact itemStep)
      refine ⟨_, step, ?_⟩
      -- the target's restrictions move onto the marker's reading
      have targetSide : ProcEquiv ambientCoreCalc ambientBlock free bound
          (Prenex.restricts ambientBlock owned (Prenex.body ambientBlock
            (beforeRead.map (liftBVars 0 owned) ++ middle :: afterRead.map (liftBVars 0 owned))))
          (Prenex.body ambientBlock (beforeRead ++ stepped :: afterRead)) := by
        refine .trans _ _ _ (restricts_body_middle owned beforeMembers afterMembers middleTyped)
          (body_congr (beforeMembers.append (Members.cons
            (restricts_typed (language := ambientCoreCalc) (block := ambientBlock) owned middleTyped) afterMembers)) ?_)
        exact forall₂_middle (fun _ => .refl _) middleRelated _ _
      -- the source's result: the stepped item beside the other items, padded
      have restIs : ((readPlaced (g + 3) parent list).map padA).eraseIdx (beforeRead.map padA).length =
          beforeRead.map padA ++ afterRead.map padA := by
        rw [itemsSplit, List.eraseIdx_append_of_length_le (Nat.le_refl _), Nat.sub_self, List.eraseIdx_cons_zero]
      rw [restIs]
      have paddedRelated : ∀ items : List Pattern, Members ambientCoreCalc ambientBlock free bound items →
          (∀ item ∈ items, isObjectPattern item = true) →
          List.Forall₂ (ProcEquiv ambientCoreCalc ambientBlock free bound) (items.map padA) items := by
        intro items itemsMembers itemsObjects
        refine List.forall₂_map_left_iff.mpr (List.forall₂_same.mpr fun item inItems => ?_)
        exact Relation.EqvGen.symm _ _ (padA_equivalent (size item + 1) (Nat.lt_succ_self _)
          (itemsMembers item inItems) (itemsObjects item inItems))
      have beforeObjects : ∀ item ∈ beforeRead, isObjectPattern item = true := fun item inBefore =>
        sourceObjects item (by rw [sourceIs]; exact List.mem_append_left _ inBefore)
      have afterObjects : ∀ item ∈ afterRead, isObjectPattern item = true := fun item inAfter =>
        sourceObjects item (by rw [sourceIs]; exact List.mem_append_right _ (List.mem_cons_of_mem _ inAfter))
      have paddedMembers : Members ambientCoreCalc ambientBlock free bound
          (stepped :: (beforeRead.map padA ++ afterRead.map padA)) := by
        intro item inItems
        rcases List.mem_cons.mp inItems with rfl | inRest
        · exact steppedTyped
        · rcases List.mem_append.mp inRest with inBefore | inAfter
          · obtain ⟨original, originalIn, rfl⟩ := List.mem_map.mp inBefore
            exact padA_typed (beforeMembers original originalIn) (beforeObjects original originalIn)
          · obtain ⟨original, originalIn, rfl⟩ := List.mem_map.mp inAfter
            exact padA_typed (afterMembers original originalIn) (afterObjects original originalIn)
      have sourceSide : ProcEquiv ambientCoreCalc ambientBlock free bound
          (.collection .hashBag (stepped :: (beforeRead.map padA ++ afterRead.map padA)) none)
          (Prenex.body ambientBlock (beforeRead ++ stepped :: afterRead)) := by
        refine .trans _ _ _ (bag_body_equivalent (language := ambientCoreCalc) (block := ambientBlock) paddedMembers) ?_
        refine .trans _ _ _ (body_congr (second := stepped :: (beforeRead ++ afterRead))
          paddedMembers (.cons (.refl _) ?_)) ?_
        · rw [← List.map_append]
          exact paddedRelated _ (beforeMembers.append afterMembers) fun item inItems => by
            rcases List.mem_append.mp inItems with inBefore | inAfter
            · exact beforeObjects item inBefore
            · exact afterObjects item inAfter
        · exact body_perm_equivalent (Members.cons steppedTyped (beforeMembers.append afterMembers))
            List.perm_middle.symm
      exact .trans _ _ _ sourceSide (Relation.EqvGen.symm _ _ targetSide)


/-- A piece whose places are all touched sits at no untouched place. -/
theorem placedAt_untouched {piece place : Pattern} {touched : List Pattern}
    (pieceTouched : ∀ at', placeAt piece = some at' → at' ∈ touched) (notTouched : place ∉ touched) :
    placedAt place piece = false := by
  cases sits : placeAt piece with
  | none => simp [placedAt, sits]
  | some at' =>
      have different : at' ≠ place := fun same => notTouched (same ▸ pieceTouched at' sits)
      simp [placedAt, sits, different]

/-- **A marker reaction below a place reads, from the place, as a step** of the pure calculus. -/
theorem path_step {bound : List TypeExpr} {count : Nat} {components : List Pattern} {depth : Nat → Nat}
    (children : ∀ component ∈ components, ∀ child, childOf component = some child →
      ∃ index < count, child = .bvar index)
    (grows : ∀ component ∈ components, ∀ index child, index < count → child < count →
      placeAt component = some (.bvar index) → childOf component = some (.bvar child) → depth index < depth child)
    (unique : ∀ child, (components.filter fun component => childOf component == some child).length ≤ 1)
    (markersOf : ∀ component ∈ components, ∀ child, childOf component = some child →
      ∃ label parent name, label ∈ markers ∧ component = .apply label [parent, child, name] ∧
        isVariable name = true)
    (typed : Members locatedCalc locatedBlock free bound components)
    {redexPlace capability marker marker' home : Pattern} {touched : List Pattern} {owned : Nat}
    {group : List Pattern}
    (groupPlaced : ∀ component ∈ group, ∀ at', placeAt component = some at' →
      at' = liftBVars 0 owned home ∨ ∃ index < owned, at' = .bvar index)
    (groupTyped : Members locatedCalc locatedBlock free (List.replicate owned nameType ++ bound) group)
    (marker'Typed : HasType locatedCalc free bound marker' procType)
    (homeTouched : home ∈ touched)
    (capabilityTouched : ∀ at', placeAt capability = some at' → at' ∈ touched)
    (markerTouched : ∀ at', placeAt marker = some at' → at' ∈ touched)
    (marker'Touched : ∀ at', placeAt marker' = some at' → at' ∈ touched)
    {Holds : List Pattern → Prop}
    (holdsKeep : ∀ list place, Holds list → place ∉ touched → Holds (list.filter fun other => !placedAt place other))
    (holdsTouched : ∀ list, Holds list → ∀ start, Reaches list start redexPlace → ∀ at' ∈ touched,
      Reaches list start at')
    (holdsHere : ∀ list, Holds list → ∃ component ∈ list, placedAt redexPlace component = true)
    {extra : Nat}
    (localStep : ∀ list, Holds list → list.Sublist components → ∀ fuel, 3 * sizeList list + extra ≤ fuel →
      ∃ result, AmbNuRawStep (.collection .hashBag ((readPlaced fuel redexPlace list).map padA) none) result ∧
        ProcEquiv ambientCoreCalc ambientBlock free bound result (Prenex.restricts ambientBlock owned
          (Prenex.body ambientBlock (readPlaced fuel (liftBVars 0 owned redexPlace)
            ((reactList capability marker marker' list).map (liftBVars 0 owned) ++ group))))) :
    ∀ {list : List Pattern} {place target : Pattern}, Reaches list place target → target = redexPlace →
      list.Sublist components → Holds list → ∀ fuel, 3 * sizeList list + extra + 3 ≤ fuel →
      ∃ result, AmbNuRawStep (.collection .hashBag ((readPlaced fuel place list).map padA) none) result ∧
        ProcEquiv ambientCoreCalc ambientBlock free bound result (Prenex.restricts ambientBlock owned
          (Prenex.body ambientBlock (readPlaced fuel (liftBVars 0 owned place)
            ((reactList capability marker marker' list).map (liftBVars 0 owned) ++ group)))) :=
  path_step_of children grows unique markersOf typed groupPlaced groupTyped homeTouched
    (fun {_} i hi {_} inner => .par i hi inner) (fun name {_ _} inner => .ambient name inner) bag_single_step
    (react := reactList capability marker marker')
    (fun _ place notTouched => reactList_at (placedAt_untouched capabilityTouched notTouched)
      (placedAt_untouched markerTouched notTouched) (placedAt_untouched marker'Touched notTouched))
    (fun _ place notTouched => reactList_elsewhere (placedAt_untouched markerTouched notTouched)
      (placedAt_untouched marker'Touched notTouched))
    (fun _ members component inReacted => by
      rcases mem_reactList inReacted with inList | rfl
      · exact members component inList
      · exact marker'Typed)
    holdsKeep holdsTouched holdsHere localStep

/-! ## Reading the redex's components -/

open Mettapedia.GSLT.LanguageDef.RestrictionBlocks (decompose)
open Mettapedia.Languages.ProcessCalculi.Ambient.Decoding (capabilities ambientCapability decodeForm
  not_marker_of_capability)

/-- **A capability of a variable name reads as the capability** on its continuation's reading at its place. -/
theorem readComponent_capability (fuel : Nat) (place : Pattern) {label : String} (listed : label ∈ capabilities)
    {at' name continuation : Pattern} (isVar : isVariable name = true) (elsewhere : List Pattern) :
    readComponent (fuel + 1) place (.apply label [at', name, continuation]) elsewhere =
      .apply (ambientCapability label)
        [name, Prenex.toPattern ambientBlock (decodeForm fuel place (decompose locatedBlock continuation))] := by
  simp [readComponent, not_marker_of_capability listed, listed, isVar]

/-- A padded capability of a variable name pads its continuation. -/
theorem padA_capability {label : String} (notAmbient : label ≠ "AAmb") {name continuation : Pattern}
    (isVar : isVariable name = true) :
    padA (.apply label [name, continuation]) = .apply label [name, padA continuation] := by
  simp [padA, padAList, padApply, notAmbient, padA_variable isVar]

/-- Among a continuation's components, its own locations reach only its own locations. -/
theorem reaches_owned {owned : Nat} {group : List Pattern}
    (groupChildren : ∀ component ∈ group, ∀ child, childOf component = some child →
      ∃ index < owned, child = .bvar index) :
    ∀ {list : List Pattern} {place target : Pattern}, (∀ component ∈ list, component ∈ group) →
      Reaches list place target → (∃ index < owned, place = .bvar index) → ∃ index < owned, target = .bvar index := by
  intro list place target within reached
  induction reached with
  | here => exact id
  | @down list place child target marker member isPlaced isChild below recurse =>
      intro _
      exact recurse (fun component inFiltered => within component (List.mem_filter.mp inFiltered).1)
        (groupChildren marker (within marker member) child isChild)

/-- **A continuation's component reads alike beside other components** that sit at none of its own locations. -/
theorem group_reads {owned : Nat} {group others : List Pattern}
    (groupChildren : ∀ component ∈ group, ∀ child, childOf component = some child →
      ∃ index < owned, child = .bvar index)
    (othersApart : ∀ component ∈ others, ∀ at', placeAt component = some at' → ∀ index < owned, at' ≠ .bvar index)
    (fuel : Nat) (place component : Pattern)
    (componentChildren : ∀ child, childOf component = some child → ∃ index < owned, child = .bvar index) :
    readComponent fuel place component (others ++ group) = readComponent fuel place component group := by
  cases fuel with
  | zero => rfl
  | succ fuel =>
      refine readComponent_congr fun child isChild => ?_
      have childOwned := componentChildren child isChild
      refine (readPlaced_reach_congr fuel (first := group) fun at' reached => ?_).symm
      obtain ⟨index', below', rfl⟩ := reaches_owned groupChildren (fun _ inGroup => inGroup) reached childOwned
      have othersNone : others.filter (placedAt (.bvar index')) = [] :=
        List.filter_eq_nil_iff.mpr fun other otherIn isPlaced => by
          cases sits : placeAt other with
          | none => simp [placedAt, sits] at isPlaced
          | some at'' =>
              have same : at'' = .bvar index' := by simpa [placedAt, sits] using isPlaced
              exact othersApart other otherIn at'' sits index' below' same
      rw [List.filter_append, othersNone, List.nil_append]


/-! ## Opening at its place -/

open Mettapedia.Languages.ProcessCalculi.Ambient.Decoding (placeAt_capability size_le_sizeList decodeForm_settled
  decodeForm_typed decode_rename readPlaced_unreached restricts_body_split)
open Mettapedia.GSLT.LanguageDef.RestrictionBlocks (restricts_congr rename_body liftBVars_eq_rename shiftAbove)

/-- A component of a nested block reaching back to its own place from its location is none. -/
theorem not_reaches_back {count : Nat} {components : List Pattern} {depth : Nat → Nat}
    (children : ∀ component ∈ components, ∀ child, childOf component = some child →
      ∃ index < count, child = .bvar index)
    (grows : ∀ component ∈ components, ∀ index child, index < count → child < count →
      placeAt component = some (.bvar index) → childOf component = some (.bvar child) → depth index < depth child)
    {list : List Pattern} (within : ∀ component ∈ list, component ∈ components) {place child component : Pattern}
    (member : component ∈ list) (isPlaced : placedAt place component = true) (isChild : childOf component = some child) :
    ¬ Reaches (list.filter fun other => !placedAt place other) child place := by
  intro back
  have same := reaches_antisymm children grows within
    (fun other inFiltered => within other (List.mem_filter.mp inFiltered).1)
    (.down member isPlaced isChild .here) back
  subst same
  obtain ⟨index, below, rfl⟩ := children component (within _ member) _ isChild
  have := grows component (within _ member) index index below below (by simpa [placedAt] using isPlaced) isChild
  omega


open Mettapedia.Languages.ProcessCalculi.Ambient.Decoding (isVariable_lift shiftAbove_injective size_pos)

/-- **An opening at its place reads as an opening there**: the capability and the ambient it opens, read at the
place, step to the continuation beside the ambient's content, which is what the reacted components read as there,
under the continuation's restrictions. -/
theorem open_local {bound : List TypeExpr} {count : Nat} {components : List Pattern} {depth : Nat → Nat}
    (children : ∀ component ∈ components, ∀ child, childOf component = some child →
      ∃ index < count, child = .bvar index)
    (grows : ∀ component ∈ components, ∀ index child, index < count → child < count →
      placeAt component = some (.bvar index) → childOf component = some (.bvar child) → depth index < depth child)
    (unique : ∀ child, (components.filter fun component => childOf component == some child).length ≤ 1)
    (typed : Members locatedCalc locatedBlock free bound components)
    {place location name continuation : Pattern} {owned : Nat} {group : List Pattern}
    (nameVar : isVariable name = true)
    (decomposed : decompose locatedBlock continuation = ⟨owned, group⟩)
    (groupPlaced : ∀ component ∈ group, ∀ at', placeAt component = some at' →
      at' = liftBVars 0 owned place ∨ ∃ index < owned, at' = .bvar index)
    (groupChildren : ∀ component ∈ group, ∀ child, childOf component = some child →
      ∃ index < owned, child = .bvar index)
    (groupTyped : Members locatedCalc locatedBlock free (List.replicate owned nameType ++ bound) group)
    {list : List Pattern} (sub : list.Sublist components)
    (capabilityIn : Pattern.apply "LOpen" [place, name, continuation] ∈ list)
    (markerIn : Pattern.apply "LAmb" [place, location, name] ∈ list)
    (fuel : Nat) (enough : 3 * sizeList list + 4 ≤ fuel) :
    ∃ result, AmbNuRawStep (.collection .hashBag ((readPlaced fuel place list).map padA) none) result ∧
      ProcEquiv ambientCoreCalc ambientBlock free bound result (Prenex.restricts ambientBlock owned
        (Prenex.body ambientBlock (readPlaced fuel (liftBVars 0 owned place)
          ((reactList (.apply "LOpen" [place, name, continuation]) (.apply "LAmb" [place, location, name])
            (.apply "LOpened" [place, location, name]) list).map (liftBVars 0 owned) ++ group)))) := by
  have within : ∀ component ∈ list, component ∈ components := fun component inList => sub.subset inList
  obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 3 := ⟨fuel - 3, by omega⟩
  set capability := Pattern.apply "LOpen" [place, name, continuation] with capabilityIs
  set marker := Pattern.apply "LAmb" [place, location, name] with markerIs
  set marker' := Pattern.apply "LOpened" [place, location, name] with marker'Is
  have openListed : "LOpen" ∈ capabilities := by simp [capabilities]
  have capabilityPlaced : placedAt place capability = true := by
    simp [placedAt, capabilityIs, placeAt_capability openListed]
  have markerPlaced : placedAt place marker = true := by
    simp [placedAt, markerIs, placeAt_ofMarker (show "LAmb" ∈ markers by simp [markers])]
  have marker'Placed : placedAt place marker' = true := by
    simp [placedAt, marker'Is, placeAt_ofMarker (show "LOpened" ∈ markers by simp [markers])]
  set here := list.filter (placedAt place) with hereIs
  set elsewhere := list.filter fun other => !placedAt place other with elsewhereIs
  have capabilityHere : capability ∈ here := List.mem_filter.mpr ⟨capabilityIn, capabilityPlaced⟩
  have markerHere : marker ∈ here := List.mem_filter.mpr ⟨markerIn, markerPlaced⟩
  -- the capability and the marker among the components at the place
  obtain ⟨i, hi, capabilityAt⟩ := List.getElem_of_mem capabilityHere
  have markerRest : marker ∈ here.eraseIdx i := by
    obtain ⟨j₀, hj₀, markerAt₀⟩ := List.getElem_of_mem markerHere
    refine List.mem_eraseIdx_iff_getElem.mpr ⟨j₀, hj₀, fun same => ?_, markerAt₀⟩
    subst same
    rw [capabilityAt] at markerAt₀
    simp [capabilityIs, markerIs] at markerAt₀
  obtain ⟨j, hj, markerAt⟩ := List.getElem_of_mem markerRest
  set others := (here.eraseIdx i).eraseIdx j with othersIs
  have hereSplit : here.Perm (capability :: marker :: others) := by
    have split := perm_two here i hi j hj
    rwa [capabilityAt, markerAt] at split
  have hereSub : here.Sublist components := List.filter_sublist.trans sub
  have markerOnce : marker ∉ others := by
    intro inOthers
    have markerChild : (childOf marker == some location) = true := by simp [markerIs, childOf, markers]
    have capabilityChild : (childOf capability == some location) = false := by
      simp [capabilityIs, childOf, markers]
    have counted := (hereSplit.filter (fun component => childOf component == some location)).length_eq
    simp only [List.filter_cons, markerChild, capabilityChild, if_true, Bool.false_eq_true, if_false,
      List.length_cons] at counted
    have inFiltered : marker ∈ others.filter (fun component => childOf component == some location) :=
      List.mem_filter.mpr ⟨inOthers, markerChild⟩
    have positive := List.length_pos_of_mem inFiltered
    have atMost := le_trans (hereSub.filter (fun component => childOf component == some location)).length_le
      (unique location)
    omega
  have othersHere : ∀ component ∈ others, component ∈ here := fun component inOthers =>
    hereSplit.symm.subset (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ inOthers))
  -- the source: the opening on the padded items at the place
  set readS := fun component => readComponent (f + 2) place component elsewhere with readSIs
  have sourceIs : (readPlaced (f + 3) place list).map padA = here.map (padA ∘ readS) := by
    rw [readPlaced_succ, List.map_map]
  set continuationRead := Prenex.toPattern ambientBlock (decodeForm (f + 1) place (decompose locatedBlock continuation))
    with continuationReadIs
  set content := Prenex.body ambientBlock (readPlaced (f + 1) location elsewhere) with contentIs
  have capabilityRead : (padA ∘ readS) capability = .apply "AOpen" [name, padA continuationRead] := by
    simp only [Function.comp, readSIs, capabilityIs]
    rw [readComponent_capability (f + 1) place openListed nameVar, show ambientCapability "LOpen" = "AOpen" by decide,
      padA_capability (by decide) nameVar]
  have markerRead : (padA ∘ readS) marker = .apply "AAmb" [name, asBag (padA content)] := by
    simp only [Function.comp, readSIs, markerIs]
    rw [readComponent_amb (f + 1) place nameVar, padA_amb nameVar]
  have hiItems : i < (here.map (padA ∘ readS)).length := by simpa using hi
  have capabilityItem : (here.map (padA ∘ readS))[i] = .apply "AOpen" [name, padA continuationRead] := by
    rw [List.getElem_map, capabilityAt, capabilityRead]
  have erasedMap : (here.map (padA ∘ readS)).eraseIdx i = (here.eraseIdx i).map (padA ∘ readS) :=
    List.eraseIdx_map _ _ _
  have hjItems : j < ((here.map (padA ∘ readS)).eraseIdx i).length := by rw [erasedMap]; simpa using hj
  have markerItem : ((here.map (padA ∘ readS)).eraseIdx i)[j] = .apply "AAmb" [name, asBag (padA content)] := by
    refine (List.getElem_of_eq erasedMap hjItems).trans ?_
    rw [List.getElem_map, markerAt, markerRead]
  have step := AmbNuRawStep.open (tail := none) i hiItems j hjItems name (padA continuationRead)
    (asBag (padA content)) capabilityItem markerItem
  have restIs : ((here.map (padA ∘ readS)).eraseIdx i).eraseIdx j = others.map (padA ∘ readS) := by
    rw [erasedMap, List.eraseIdx_map]
  rw [restIs] at step
  rw [sourceIs]
  refine ⟨_, step, ?_⟩
  -- the target: the reacted components at the lifted place
  have reactedHere : (reactList capability marker marker' list).filter (placedAt place) =
      reactList capability marker marker' here :=
    reactList_filter (by rw [marker'Placed, markerPlaced]) list
  have notElsewhere : ∀ {piece : Pattern}, placedAt place piece = true → piece ∉ elsewhere :=
    fun placed inElsewhere => by simp [elsewhereIs, placed] at inElsewhere
  have reactedElsewhere : (reactList capability marker marker' list).filter (fun other => !placedAt place other) =
      elsewhere := by
    rw [reactList_filter (by rw [marker'Placed, markerPlaced])]
    exact reactList_untouched (notElsewhere capabilityPlaced) (notElsewhere markerPlaced)
  set groupHere := group.filter (placedAt (liftBVars 0 owned place)) with groupHereIs
  set groupDeep := group.filter fun other => !placedAt (liftBVars 0 owned place) other with groupDeepIs
  set readT := fun component => readComponent (f + 2) (liftBVars 0 owned place) component
    (elsewhere.map (liftBVars 0 owned) ++ groupDeep) with readTIs
  have hereT : ((reactList capability marker marker' list).map (liftBVars 0 owned) ++ group).filter
      (placedAt (liftBVars 0 owned place)) = (reactList capability marker marker' here).map (liftBVars 0 owned) ++
        groupHere := by
    rw [List.filter_append, filter_lift_at, reactedHere]
  have elsewhereT : ((reactList capability marker marker' list).map (liftBVars 0 owned) ++ group).filter
      (fun other => !placedAt (liftBVars 0 owned place) other) = elsewhere.map (liftBVars 0 owned) ++ groupDeep := by
    rw [List.filter_append, filter_lift_elsewhere, reactedElsewhere]
  have targetIs : readPlaced (f + 3) (liftBVars 0 owned place)
      ((reactList capability marker marker' list).map (liftBVars 0 owned) ++ group) =
      ((reactList capability marker marker' here).map (liftBVars 0 owned)).map readT ++ groupHere.map readT := by
    rw [readPlaced_succ, hereT, elsewhereT, List.map_append]
  rw [targetIs]
  -- the deep part of the continuation sits at its own locations
  have groupDeepPlaced : ∀ component ∈ groupDeep, ∀ at', placeAt component = some at' →
      at' = liftBVars 0 owned place ∨ ∃ index < owned, at' = .bvar index := fun component inDeep =>
    groupPlaced component (List.mem_filter.mp inDeep).1
  have groupDeepOwned : ∀ component ∈ groupDeep, ∀ at', placeAt component = some at' →
      ∃ index < owned, at' = .bvar index := by
    intro component inDeep at' sits
    rcases groupDeepPlaced component inDeep at' sits with atPlace | isOwned
    · have := (List.mem_filter.mp inDeep).2
      simp [placedAt, sits, atPlace] at this
    · exact isOwned
  have groupDeepChildren : ∀ component ∈ groupDeep, ∀ child, childOf component = some child →
      ∃ index < owned, child = .bvar index := fun component inDeep =>
    groupChildren component (List.mem_filter.mp inDeep).1
  have liftedApart : ∀ component ∈ elsewhere.map (liftBVars 0 owned), ∀ at', placeAt component = some at' →
      ∀ index < owned, at' ≠ .bvar index := by
    intro component inLifted at' sits index below same
    obtain ⟨original, -, rfl⟩ := List.mem_map.mp inLifted
    rw [liftBVars_eq_rename, Mettapedia.Languages.ProcessCalculi.Ambient.Decoding.placeAt_rename] at sits
    cases found : placeAt original with
    | none => rw [found] at sits; cases sits
    | some originalAt =>
        rw [found, Option.map_some, Option.some.injEq, ← liftBVars_eq_rename] at sits
        rw [← sits] at same
        exact lift_ne_owned below same
  -- each reacted component, read
  have othersRead : ∀ component ∈ others,
      readT (liftBVars 0 owned component) = liftBVars 0 owned (readS component) := by
    intro component inOthers
    have inHere := othersHere component inOthers
    exact readComponent_lifted groupDeepPlaced (f + 2) place component fun child isChild =>
      not_reaches_back children grows within (List.mem_filter.mp inHere).1 (List.mem_filter.mp inHere).2 isChild
  have liftedMarker' : liftBVars 0 owned marker' =
      .apply "LOpened" [liftBVars 0 owned place, liftBVars 0 owned location, liftBVars 0 owned name] := by
    simp [marker'Is, liftBVars, Mettapedia.OSLF.MeTTaIL.Substitution.liftBVarsList_eq_map]
  have openedRead : readT (liftBVars 0 owned marker') = liftBVars 0 owned content := by
    simp only [readTIs]
    rw [liftedMarker', readComponent_opened (f + 1) _ (by rw [isVariable_lift]; exact nameVar)]
    rw [readPlaced_unreached (f + 1) _ _ _ fun component inDeep at' sits reached => ?_]
    · have liftIs : liftBVars 0 owned = rename (shiftAbove 0 owned) := funext (liftBVars_eq_rename 0 owned)
      rw [contentIs, liftIs, rename_body, (decode_rename (f + 1) (shiftAbove_injective 0 owned)).2.1]
    · rcases reaches_lifted groupDeepPlaced reached with ⟨original, rfl, -⟩ | back
      · obtain ⟨index, below, same⟩ := groupDeepOwned component inDeep _ sits
        exact lift_ne_owned below same
      · exact not_reaches_back children grows within markerIn markerPlaced (by simp [markerIs, childOf, markers])
          back
  have groupRead : ∀ component ∈ groupHere, readT component =
      readComponent (f + 2) (liftBVars 0 owned place) component groupDeep := by
    intro component inHere'
    exact group_reads groupDeepChildren liftedApart (f + 2) _ component
      (groupChildren component (List.mem_filter.mp inHere').1)
  -- the continuation, read at the place
  have massBound : 3 * Prenex.mass ⟨owned, group⟩ + 3 ≤ f + 1 := by
    have massLe := Mettapedia.GSLT.LanguageDef.RestrictionBlocks.mass_decompose (block := locatedBlock) continuation
    rw [decomposed] at massLe
    have capabilitySize : size continuation + 3 ≤ size capability := by
      simp only [capabilityIs, size, sizeList]
      have := size_pos place
      have := size_pos name
      omega
    have listSize := size_le_sizeList capabilityIn
    omega
  have continuationIs : continuationRead = Prenex.restricts ambientBlock owned (Prenex.body ambientBlock
      (groupHere.map fun component => readComponent (f + 2) (liftBVars 0 owned place) component groupDeep)) := by
    rw [continuationReadIs, decomposed, decodeForm_settled place _ massBound (show 3 * _ + 3 ≤ f + 4 by omega)]
    simp only [decodeForm, Prenex.toPattern]
    rw [readPlaced_succ]
  -- typing
  have elsewhereMembers : Members locatedCalc locatedBlock free bound elsewhere := fun component inElsewhere =>
    typed component (within component (List.mem_filter.mp inElsewhere).1)
  have readSTyped : ∀ component ∈ others, HasType ambientCoreCalc free bound (readS component) procType :=
    fun component inOthers => (decode_typed (f + 2)).2.2 place component elsewhere
      (typed component (within component (List.mem_filter.mp (othersHere component inOthers)).1)) elsewhereMembers
  have readSObject : ∀ component, isObjectPattern (readS component) = true := fun component =>
    (decode_object (f + 2)).2.2 place component elsewhere
  have contentTyped : HasType ambientCoreCalc free bound content procType :=
    body_typed ((decode_typed (f + 1)).2.1 location elsewhere elsewhereMembers)
  have contentObject : isObjectPattern content = true :=
    Mettapedia.GSLT.LanguageDef.RestrictionBlocks.isObject_toPattern (form := ⟨0, readPlaced (f + 1) location elsewhere⟩)
      ((decode_object (f + 1)).2.1 location elsewhere)
  have continuationTyped : HasType ambientCoreCalc free bound continuationRead procType := by
    rw [continuationReadIs, decomposed]
    exact decodeForm_typed (f + 1) place groupTyped
  have continuationObject : isObjectPattern continuationRead = true :=
    Mettapedia.GSLT.LanguageDef.RestrictionBlocks.isObject_toPattern ((decode_object (f + 1)).1 place _)
  have keptMembers : Members ambientCoreCalc ambientBlock free bound (content :: others.map readS) := by
    intro item inItems
    rcases List.mem_cons.mp inItems with rfl | inRest
    · exact contentTyped
    · obtain ⟨original, inOthers, rfl⟩ := List.mem_map.mp inRest
      exact readSTyped original inOthers
  have groupItems : groupHere.map readT = groupHere.map
      (fun component => readComponent (f + 2) (liftBVars 0 owned place) component groupDeep) :=
    List.map_congr_left groupRead
  have groupMembers : Members ambientCoreCalc ambientBlock free (List.replicate owned nameType ++ bound)
      (groupHere.map readT) := by
    rw [groupItems]
    have groupReading := (decode_typed (f + 3)).2.1 (liftBVars 0 owned place) group groupTyped
    rw [readPlaced_succ] at groupReading
    exact groupReading
  have liftedKept : Members ambientCoreCalc ambientBlock free (List.replicate owned nameType ++ bound)
      ((content :: others.map readS).map (liftBVars 0 owned)) := by
    have lifted := Mettapedia.GSLT.LanguageDef.RestrictionBlocks.Members.lift (language := ambientCoreCalc)
      (block := ambientBlock) (List.replicate owned nameType) keptMembers
    rwa [List.length_replicate] at lifted
  -- the reacted components at the place: the opened marker and the others, in another order
  have reactedPerm : (reactList capability marker marker' here).Perm (marker' :: others) := by
    unfold reactList
    have erasedPerm : (here.erase capability).Perm (marker :: others) := by
      have erased := hereSplit.erase capability
      simpa using erased
    have mapped := erasedPerm.map (fun component => if component = marker then marker' else component)
    rw [List.map_cons, if_pos rfl] at mapped
    have othersSame : others.map (fun component => if component = marker then marker' else component) = others := by
      conv_rhs => rw [← List.map_id others]
      exact List.map_congr_left fun component inOthers => by
        have different : component ≠ marker := fun same => markerOnce (same ▸ inOthers)
        simp [different]
    rwa [othersSame] at mapped
  have itemsPerm : (((reactList capability marker marker' here).map (liftBVars 0 owned)).map readT).Perm
      ((content :: others.map readS).map (liftBVars 0 owned)) := by
    have mapped := (reactedPerm.map (liftBVars 0 owned)).map readT
    refine mapped.trans (.of_eq ?_)
    simp only [List.map_cons, List.map_map]
    rw [openedRead]
    congr 1
    exact List.map_congr_left fun component inOthers => othersRead component inOthers
  -- assembled
  have targetSide : ProcEquiv ambientCoreCalc ambientBlock free bound
      (Prenex.restricts ambientBlock owned (Prenex.body ambientBlock
        (((reactList capability marker marker' here).map (liftBVars 0 owned)).map readT ++ groupHere.map readT)))
      (Prenex.body ambientBlock (continuationRead :: content :: others.map readS)) := by
    have allMembers : Members ambientCoreCalc ambientBlock free (List.replicate owned nameType ++ bound)
        (((reactList capability marker marker' here).map (liftBVars 0 owned)).map readT ++ groupHere.map readT) :=
      fun item inItems => (liftedKept.append groupMembers) item
        ((itemsPerm.append_right _).subset inItems)
    refine .trans _ _ _ (restricts_congr (language := ambientCoreCalc) (block := ambientBlock) owned
      (body_perm_equivalent allMembers (itemsPerm.append_right _))) ?_
    refine .trans _ _ _ (restricts_body_split owned keptMembers groupMembers) ?_
    rw [groupItems, ← continuationIs]
    exact .refl _
  have sourceMembers : Members ambientCoreCalc ambientBlock free bound
      (padA continuationRead :: asBag (padA content) :: others.map (padA ∘ readS)) := by
    intro item inItems
    simp only [List.mem_cons] at inItems
    rcases inItems with rfl | rfl | inRest
    · exact padA_typed continuationTyped continuationObject
    · exact (Mettapedia.GSLT.LanguageDef.RestrictionBlocks.SortedEquiv.typed_iff
        (asBag_equivalent (padA_typed contentTyped contentObject))).mp (padA_typed contentTyped contentObject)
    · obtain ⟨original, inOthers, rfl⟩ := List.mem_map.mp inRest
      exact padA_typed (readSTyped original inOthers) (readSObject original)
  have sourceSide : ProcEquiv ambientCoreCalc ambientBlock free bound
      (.collection .hashBag (padA continuationRead :: asBag (padA content) :: others.map (padA ∘ readS)) none)
      (Prenex.body ambientBlock (continuationRead :: content :: others.map readS)) := by
    refine .trans _ _ _ (bag_body_equivalent (language := ambientCoreCalc) (block := ambientBlock) sourceMembers) ?_
    refine body_congr sourceMembers (.cons ?_ (.cons ?_ ?_))
    · exact Relation.EqvGen.symm _ _ (padA_equivalent (size continuationRead + 1) (Nat.lt_succ_self _)
        continuationTyped continuationObject)
    · exact Relation.EqvGen.symm _ _ (.trans _ _ _
        (padA_equivalent (size content + 1) (Nat.lt_succ_self _) contentTyped contentObject)
        (asBag_equivalent (padA_typed contentTyped contentObject)))
    · refine List.forall₂_map_left_iff.mpr (List.forall₂_map_right_iff.mpr (List.forall₂_same.mpr fun component
        inOthers => ?_))
      exact Relation.EqvGen.symm _ _ (padA_equivalent (size (readS component) + 1) (Nat.lt_succ_self _)
        (readSTyped component inOthers) (readSObject component))
  exact .trans _ _ _ sourceSide (Relation.EqvGen.symm _ _ targetSide)


/-! ## Reading lifted components where nothing changed -/

open Mettapedia.Languages.ProcessCalculi.Ambient.Decoding (decode_settle)

/-- Reaching among lifted components is reaching among the components, lifted. -/
theorem reaches_map_lift (owned : Nat) : ∀ {list : List Pattern} {place target : Pattern},
    Reaches (list.map (liftBVars 0 owned)) (liftBVars 0 owned place) target →
    ∃ original, target = liftBVars 0 owned original ∧ Reaches list place original := by
  intro list place target reached
  generalize listIs : list.map (liftBVars 0 owned) = lifted at reached
  generalize placeIs : liftBVars 0 owned place = liftedPlace at reached
  induction reached generalizing list place with
  | here => subst placeIs; exact ⟨place, rfl, .here⟩
  | @down components liftedPlace child target marker member isPlaced isChild below recurse =>
      subst listIs placeIs
      obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp member
      rw [placedAt_lift] at isPlaced
      rw [childOf_lift] at isChild
      cases found : childOf original with
      | none => rw [found] at isChild; cases isChild
      | some originalChild =>
          rw [found, Option.map_some, Option.some.injEq] at isChild
          subst isChild
          obtain ⟨deep, rfl, deeper⟩ := recurse (filter_lift_elsewhere owned place list).symm rfl
          exact ⟨deep, rfl, .down originalMember isPlaced found deeper⟩

/-- **A lifted component reads as its reading, lifted**, among components that, at every place it reaches, are the
original ones there, lifted. -/
theorem readComponent_lift_congr {owned : Nat} {place component : Pattern} {original changed : List Pattern}
    (fuel : Nat)
    (same : ∀ child, childOf component = some child → ∀ at', Reaches original child at' →
      changed.filter (placedAt (liftBVars 0 owned at')) = (original.filter (placedAt at')).map (liftBVars 0 owned)) :
    readComponent fuel (liftBVars 0 owned place) (liftBVars 0 owned component) changed =
      liftBVars 0 owned (readComponent fuel place component original) := by
  have liftIs : liftBVars 0 owned = rename (shiftAbove 0 owned) := funext (liftBVars_eq_rename 0 owned)
  have lifted : liftBVars 0 owned (readComponent fuel place component original) =
      readComponent fuel (liftBVars 0 owned place) (liftBVars 0 owned component)
        (original.map (liftBVars 0 owned)) := by
    rw [liftIs]
    exact ((decode_rename fuel (shiftAbove_injective 0 owned)).2.2 place component original).symm
  rw [lifted]
  cases fuel with
  | zero => rfl
  | succ fuel =>
      refine readComponent_congr fun child isChild => ?_
      rw [childOf_lift] at isChild
      cases found : childOf component with
      | none => rw [found] at isChild; cases isChild
      | some originalChild =>
          rw [found, Option.map_some, Option.some.injEq] at isChild
          subst isChild
          refine (readPlaced_reach_congr fuel (first := original.map (liftBVars 0 owned))
            fun at' reached => ?_).symm
          obtain ⟨deep, rfl, deeper⟩ := reaches_map_lift owned reached
          rw [filter_lift_at, same originalChild found deep deeper]

/-- **More fuel past three times its weight reads a place alike.** -/
theorem readPlaced_settled {first second : Nat} (place : Pattern) (components : List Pattern)
    (firstEnough : 3 * sizeList components + 2 ≤ first) (secondEnough : 3 * sizeList components + 2 ≤ second) :
    readPlaced first place components = readPlaced second place components := by
  have stable : ∀ extra fuel, 3 * sizeList components + 2 ≤ fuel →
      readPlaced fuel place components = readPlaced (fuel + extra) place components := by
    intro extra
    induction extra with
    | zero => intro fuel _; rfl
    | succ extra recurse =>
        intro fuel enough
        rw [recurse fuel enough, (decode_settle (fuel + extra)).1 place components (by omega)]
        rfl
  rcases Nat.le_total first second with order | order
  · obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le order
    exact stable extra first firstEnough
  · obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le order
    exact (stable extra second secondEnough).symm

/-- **A location no component places an ambient at is reached from nowhere else.** -/
theorem not_reaches_unmarked {list : List Pattern} {start location : Pattern}
    (unmarked : ∀ component ∈ list, childOf component ≠ some location) (different : start ≠ location) :
    ¬ Reaches list start location := fun reached => by
  obtain ⟨marker, member, isChild⟩ := Mettapedia.Languages.ProcessCalculi.Ambient.Decoding.Reaches.last reached
    different
  exact unmarked marker member isChild


/-! ## Small facts for the moves -/

/-- **A marker's location is not where it sits.** -/
theorem child_ne_place {count : Nat} {components : List Pattern} {depth : Nat → Nat}
    (children : ∀ component ∈ components, ∀ child, childOf component = some child →
      ∃ index < count, child = .bvar index)
    (grows : ∀ component ∈ components, ∀ index child, index < count → child < count →
      placeAt component = some (.bvar index) → childOf component = some (.bvar child) → depth index < depth child)
    {component place child : Pattern} (member : component ∈ components) (isPlaced : placedAt place component = true)
    (isChild : childOf component = some child) : child ≠ place := by
  rintro rfl
  obtain ⟨index, below, rfl⟩ := children component member _ isChild
  have := grows component member index index below below (by simpa [placedAt] using isPlaced) isChild
  omega

/-- A component sitting at one place does not sit at another. -/
theorem placedAt_other {component place other : Pattern} (isPlaced : placedAt place component = true)
    (different : other ≠ place) : placedAt other component = false := by
  simp only [placedAt, beq_iff_eq] at isPlaced
  simp [placedAt, isPlaced, Ne.symm different]

/-- **What sits at one place among what sits elsewhere than another is what sits there.** -/
theorem filter_at_elsewhere {place other : Pattern} (different : other ≠ place) (components : List Pattern) :
    (components.filter fun component => !placedAt place component).filter (placedAt other) =
      components.filter (placedAt other) := by
  rw [List.filter_filter]
  refine List.filter_congr fun component _ => ?_
  cases sits : placedAt other component with
  | false => simp
  | true => simp [placedAt_other sits (Ne.symm different)]

/-- Erasing by position or by the value there leaves the same members. -/
theorem eraseIdx_perm_erase {list : List Pattern} {index : Nat} (inside : index < list.length) :
    (list.eraseIdx index).Perm (list.erase list[index]) := by
  have first := (List.getElem_cons_eraseIdx_perm inside).symm
  have second := List.perm_cons_erase (List.getElem_mem inside)
  exact (first.symm.trans second).cons_inv

end Mettapedia.Languages.ProcessCalculi.Ambient.Steps
