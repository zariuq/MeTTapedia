import Mettapedia.Languages.ProcessCalculi.Ambient.DecodingStep

/-!
# Reading back canonical blocks

The canonical block of a well-located block reads back as the block (`decode_normal`), and is well-located. Normalizing
absorbs copies one at a time (`DecodingStep`), drops the restrictions left unused, reorders the rest, reads every
component's parts canonically, sorts the components and keeps one of each replication: each of these reads back
equivalently, the parts read canonically by induction on the weight of the block.

This file holds:

- reading components changed one by one, with fuel past a floor (`readPlaced_map_from`);
- one of each replication kept, at any depth (`decode_dedup`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.Ambient.Decoding

open Mettapedia.Languages.ProcessCalculi.Ambient.Comm (ambientCoreCalc coreSignature capType)

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Substitution (liftBVars)
open Mettapedia.OSLF.MeTTaIL.CanonicalBags (FreeIn freeIn_bvar)
open Mettapedia.GSLT.LanguageDef.WellSorted (HasType FreeTypeContext)
open Mettapedia.GSLT.LanguageDef.RestrictionBlocks (Prenex Members ProcEquiv body_typed body_congr body_pair_equivalent
  nil_bag_equivalent bag_body_equivalent idempotent_absorb_equivalent isReplicated dedupReplicated mem_dedupReplicated
  restricts_congr)
open Mettapedia.Languages.ProcessCalculi.Ambient.Full (ambientBlock ambientRepBlock)
open Mettapedia.Languages.ProcessCalculi.Ambient.Located (locatedCalc locatedBlock locatedRepBlock)
open Mettapedia.Languages.ProcessCalculi.Ambient.Encoding (nameType procType)

variable {free : FreeTypeContext}

/-! ## Components changed one by one, past a fuel floor -/

/-- **Components changed one by one read equivalently past a fuel floor**: a change keeping every component's place,
reading every component equivalently among equivalent surroundings at its place with fuel past the floor, reads
equivalently with fuel past the floor and twice the number of components. -/
theorem readPlaced_map_from {change : Pattern → Pattern} {low : Nat} : ∀ (fuel : Nat) {bound : List TypeExpr}
    {components : List Pattern} (place : Pattern), low + 2 * components.length + 2 ≤ fuel →
    Members locatedCalc locatedBlock free bound components →
    Members locatedCalc locatedBlock free bound (components.map change) →
    (∀ component ∈ components, placeAt (change component) = placeAt component) →
    (∀ component ∈ components, ∀ (fuel' : Nat), low ≤ fuel' → ∀ (place' : Pattern) (first second : List Pattern),
      placedAt place' component = true →
      Members locatedCalc locatedBlock free bound first → Members locatedCalc locatedBlock free bound second →
      (∀ child, childOf component = some child →
        ProcEquiv ambientCoreCalc ambientBlock free bound (Prenex.body ambientBlock (readPlaced fuel' child first))
          (Prenex.body ambientBlock (readPlaced fuel' child second))) →
      ProcEquiv ambientCoreCalc ambientBlock free bound (readComponent (fuel' + 1) place' (change component) first)
        (readComponent (fuel' + 1) place' component second)) →
    ProcEquiv ambientCoreCalc ambientBlock free bound
      (Prenex.body ambientBlock (readPlaced fuel place (components.map change)))
      (Prenex.body ambientBlock (readPlaced fuel place components))
  | 0, _, _, _, enough, _, _, _, _ => absurd enough (by omega)
  | fuel + 1, bound, components, place, enough, members, changedMembers, keepsPlace, reads => by
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
      obtain ⟨inComponents, isHere⟩ := List.mem_filter.mp inFiltered
      have shorter : (components.filter fun other => !placedAt place other).length + 1 ≤ components.length := by
        have total := List.length_eq_length_filter_add (l := components) (placedAt place)
        have positive : 0 < (components.filter (placedAt place)).length :=
          List.length_pos_of_mem (List.mem_filter.mpr ⟨inComponents, isHere⟩)
        omega
      cases fuel with
      | zero => exact absurd enough (by omega)
      | succ fuel =>
          exact reads component inComponents fuel (by omega) place _ _ isHere changedRestMembers restMembers
            fun child _ => readPlaced_map_from fuel child (by omega) restMembers changedRestMembers
              (fun other member => keepsPlace other (List.mem_filter.mp member).1)
              (fun other member => reads other (List.mem_filter.mp member).1)

/-! ## One of each replication -/

/-- Inaction beside a body is the body. -/
theorem body_unit_cons {bound : List TypeExpr} {items : List Pattern}
    (members : Members ambientCoreCalc ambientBlock free bound items) :
    ProcEquiv ambientCoreCalc ambientBlock free bound (Prenex.body ambientBlock (inaction :: items))
      (Prenex.body ambientBlock items) := by
  have unitTyped : HasType ambientCoreCalc free bound inaction procType :=
    Mettapedia.Languages.ProcessCalculi.Ambient.Comm.coreSignature.unit_typed
  exact .trans _ _ _ (Relation.EqvGen.symm _ _ (body_pair_equivalent (first := [inaction])
    (Members.cons unitTyped Members.nil) members)) (nil_bag_equivalent (body_typed members))

/-- **A second copy of a replication changes no reading**, wherever it sits. -/
theorem readPlaced_cons_replicated {argument : Pattern} :
    ∀ (fuel : Nat) {bound : List TypeExpr} {components : List Pattern} (place : Pattern),
      Pattern.apply "LRep" [argument] ∈ components → Members locatedCalc locatedBlock free bound components →
      HasType locatedCalc free bound (.apply "LRep" [argument]) procType →
      ProcEquiv ambientCoreCalc ambientBlock free bound
        (Prenex.body ambientBlock (readPlaced fuel place (.apply "LRep" [argument] :: components)))
        (Prenex.body ambientBlock (readPlaced fuel place components))
  | 0, _, _, _, _, _, _ => .refl _
  | fuel + 1, bound, components, place, again, members, typed => by
      have restMembers : Members locatedCalc locatedBlock free bound
          (components.filter fun other => !placedAt place other) :=
        fun element member => members element (List.mem_filter.mp member).1
      have itemsMembers := readPlaced_members (fuel + 1) place members
      rw [readPlaced_succ] at itemsMembers
      rw [readPlaced_succ, readPlaced_succ]
      by_cases here : placedAt place (.apply "LRep" [argument]) = true
      · -- the copy reads as a replication beside its twin
        rw [List.filter_cons_of_pos here, List.filter_cons_of_neg (by simp [here]), List.map_cons]
        have twin : readComponent fuel place (.apply "LRep" [argument])
            (components.filter fun other => !placedAt place other) ∈
            (components.filter (placedAt place)).map fun component =>
              readComponent fuel place component (components.filter fun other => !placedAt place other) :=
          List.mem_map.mpr ⟨_, List.mem_filter.mpr ⟨again, here⟩, rfl⟩
        cases fuel with
        | zero => exact body_unit_cons itemsMembers
        | succ fuel =>
            have copyTyped := itemsMembers _ twin
            have toBag := bag_body_equivalent (Members.cons copyTyped itemsMembers)
            have fromBag := bag_body_equivalent itemsMembers
            refine .trans _ _ _ (Relation.EqvGen.symm _ _ toBag) (.trans _ _ _ ?_ fromBag)
            exact idempotent_absorb_equivalent (language := ambientCoreCalc) (block := ambientRepBlock)
              (by simp [readComponent, isReplicated]) copyTyped itemsMembers twin
      · -- the copy sits elsewhere: every ambient here reads it among the others, which hold its twin
        rw [List.filter_cons_of_neg here, List.filter_cons_of_pos (by simpa using here)]
        refine body_congr ?_ (forall₂_map_map fun component inFiltered => ?_)
        · intro element member
          obtain ⟨component, inFiltered, rfl⟩ := List.mem_map.mp member
          obtain ⟨inComponents, -⟩ := List.mem_filter.mp inFiltered
          exact (decode_typed fuel).2.2 place component _ (members component inComponents)
            (Members.cons typed restMembers)
        · obtain ⟨inComponents, -⟩ := List.mem_filter.mp inFiltered
          cases fuel with
          | zero => exact .refl _
          | succ fuel =>
              refine readComponent_equivalent (members component inComponents) fun child _ => ?_
              exact readPlaced_cons_replicated fuel child (List.mem_filter.mpr ⟨again, by simpa using here⟩)
                restMembers typed

/-- **Keeping one of each replication drops only copies of replications kept.** -/
theorem dedupReplicated_split : ∀ (components : List Pattern), ∃ removed : List Pattern,
    components.Perm (dedupReplicated locatedRepBlock components ++ removed) ∧
      ∀ dropped ∈ removed, (∃ argument, dropped = .apply "LRep" [argument]) ∧
        dropped ∈ dedupReplicated locatedRepBlock components
  | [] => ⟨[], by simp [dedupReplicated], by simp⟩
  | component :: rest => by
      obtain ⟨removed, permuted, removedFacts⟩ := dedupReplicated_split rest
      unfold dedupReplicated
      split_ifs with drop
      · obtain ⟨replicated, contained⟩ := Bool.and_eq_true_iff.mp drop
        obtain ⟨argument, isRep⟩ := Mettapedia.GSLT.LanguageDef.RestrictionBlocks.eq_of_isReplicated replicated
        refine ⟨component :: removed, ?_, ?_⟩
        · exact (permuted.cons component).trans List.perm_middle.symm
        · intro dropped member
          rcases List.mem_cons.mp member with rfl | inRemoved
          · exact ⟨⟨argument, isRep⟩, mem_dedupReplicated.mpr (List.contains_iff_mem.mp contained)⟩
          · exact removedFacts dropped inRemoved
      · refine ⟨removed, permuted.cons component, fun dropped member => ?_⟩
        obtain ⟨isRep, kept⟩ := removedFacts dropped member
        exact ⟨isRep, List.mem_cons_of_mem _ kept⟩

/-- **A block keeping one of each replication reads back as the block.** -/
theorem decode_dedup {bound : List TypeExpr} (fuel : Nat) (place : Pattern) {count : Nat} {components : List Pattern}
    (members : Members locatedCalc locatedBlock free (List.replicate count nameType ++ bound) components) :
    ProcEquiv ambientCoreCalc ambientBlock free bound
      (Prenex.toPattern ambientBlock (decodeForm (fuel + 1) place
        ⟨count, dedupReplicated locatedRepBlock components⟩))
      (Prenex.toPattern ambientBlock (decodeForm (fuel + 1) place ⟨count, components⟩)) := by
  obtain ⟨removed, permuted, removedFacts⟩ := dedupReplicated_split components
  set kept := dedupReplicated locatedRepBlock components
  have keptMembers : Members locatedCalc locatedBlock free (List.replicate count nameType ++ bound) kept :=
    fun element member => members element (Mettapedia.GSLT.LanguageDef.RestrictionBlocks.dedupReplicated_subset
      components member)
  have removedTyped : ∀ dropped ∈ removed,
      HasType locatedCalc free (List.replicate count nameType ++ bound) dropped procType :=
    fun dropped member => members dropped (permuted.symm.subset (List.mem_append_right _ member))
  -- drop the copies one by one
  have dropAll : ∀ (rest : List Pattern), (∀ dropped ∈ rest, dropped ∈ removed) →
      ProcEquiv ambientCoreCalc ambientBlock free (List.replicate count nameType ++ bound)
        (Prenex.body ambientBlock (readPlaced fuel (liftBVars 0 count place) kept))
        (Prenex.body ambientBlock (readPlaced fuel (liftBVars 0 count place) (kept ++ rest))) := by
    intro rest
    induction rest with
    | nil => intro _; rw [List.append_nil]; exact .refl _
    | cons dropped rest recurse =>
        intro inRemoved
        obtain ⟨⟨argument, rfl⟩, keptMember⟩ := removedFacts _ (inRemoved _ List.mem_cons_self)
        have restMembers : Members locatedCalc locatedBlock free (List.replicate count nameType ++ bound)
            (kept ++ rest) := by
          intro element member
          rcases List.mem_append.mp member with inKept | inRest
          · exact keptMembers element inKept
          · exact removedTyped element (inRemoved element (List.mem_cons_of_mem _ inRest))
        have moved : (kept ++ Pattern.apply "LRep" [argument] :: rest).Perm
            (Pattern.apply "LRep" [argument] :: (kept ++ rest)) := List.perm_middle
        have movedMembers : Members locatedCalc locatedBlock free (List.replicate count nameType ++ bound)
            (kept ++ Pattern.apply "LRep" [argument] :: rest) :=
          fun element member => (Members.cons (removedTyped _ (inRemoved _ List.mem_cons_self)) restMembers) element
            (moved.subset member)
        exact .trans _ _ _ (recurse fun other member => inRemoved other (List.mem_cons_of_mem _ member))
          (.trans _ _ _ (Relation.EqvGen.symm _ _ (readPlaced_cons_replicated fuel _
            (List.mem_append_left _ keptMember) restMembers (removedTyped _ (inRemoved _ List.mem_cons_self))))
            (readPlaced_perm fuel _ moved.symm (Members.cons (removedTyped _ (inRemoved _ List.mem_cons_self))
              restMembers)))
  have whole := dropAll removed fun dropped member => member
  have back := readPlaced_perm (free := free) fuel (liftBVars 0 count place) permuted.symm
    (fun element member => members element (permuted.symm.subset member))
  simp only [decodeForm, Prenex.toPattern]
  exact restricts_congr (language := ambientCoreCalc) (block := ambientBlock) count (.trans _ _ _ whole back)

/-! ## Places settle -/

open Mettapedia.GSLT.LanguageDef.RestrictionBlocks (size sizeList mass_decompose decompose canonicalOf normal
  decompose_canonicalOf mass_le_size_toPattern freePast_normal_all decompose_atomic)

theorem findSome?_congr_mem {α β : Type} {first second : α → Option β} :
    ∀ {list : List α}, (∀ element ∈ list, first element = second element) → list.findSome? first = list.findSome? second
  | [], _ => rfl
  | head :: rest, same => by
      simp only [List.findSome?_cons, same head List.mem_cons_self,
        findSome?_congr_mem fun element member => same element (List.mem_cons_of_mem _ member)]

theorem findSome?_eq_of_mem {α β : Type} {choose : α → Option β} {value : β} :
    ∀ {list : List α}, (∃ element ∈ list, choose element = some value) →
      (∀ element ∈ list, choose element = none ∨ choose element = some value) → list.findSome? choose = some value
  | [], ⟨_, member, _⟩, _ => by simp at member
  | head :: rest, ⟨element, member, found⟩, only => by
      rw [List.findSome?_cons]
      rcases only head List.mem_cons_self with isNone | isSome
      · rw [isNone]
        rcases List.mem_cons.mp member with rfl | inRest
        · rw [found] at isNone; cases isNone
        · exact findSome?_eq_of_mem ⟨element, inRest, found⟩ fun other inOther => only other (List.mem_cons_of_mem _ inOther)
      · rw [isSome]

/-- **More fuel changes no place past twice the weight.** -/
theorem places_settle : ∀ (fuel : Nat),
    (∀ component, 2 * size component + 1 ≤ fuel → placeOf fuel component = placeOf (fuel + 1) component) ∧
    (∀ form : Prenex, (∀ component ∈ form.components, 2 * size component + 2 ≤ fuel) →
      outerPlace fuel form = outerPlace (fuel + 1) form)
  | 0 => ⟨fun component enough => absurd enough (by omega), fun form _ => by
      obtain ⟨count, components⟩ := form
      simp only [outerPlace, placeOf, Option.bind_none]
      exact (List.findSome?_eq_none_iff.mpr fun _ _ => rfl).symm⟩
  | fuel + 1 => by
      obtain ⟨placesBelow, outersBelow⟩ := places_settle fuel
      refine ⟨fun component enough => ?_, fun form enough => ?_⟩
      · cases component with
        | apply label arguments =>
            match arguments, enough with
            | [_, _, _], _ => simp only [placeOf]
            | [argument], enough =>
                simp only [placeOf]
                split_ifs
                · refine outersBelow _ fun inner member => ?_
                  have weight := mass_decompose (block := locatedBlock) argument
                  have inside := size_le_sizeList member
                  simp only [size, sizeList] at enough
                  simp only [Prenex.mass] at weight
                  omega
                · rfl
            | [], _ => simp only [placeOf]
            | [_, _], _ => simp only [placeOf]
            | _ :: _ :: _ :: _ :: _, _ => simp only [placeOf]
        | _ => simp only [placeOf]
      · obtain ⟨count, components⟩ := form
        simp only [outerPlace]
        exact findSome?_congr_mem fun component member => by
          rw [placesBelow component (by have := enough component member; omega)]

/-- **A place read with more fuel than its own is its place.** -/
theorem placeOf_eq_placeAt {component : Pattern} : ∀ {fuel : Nat}, 2 * size component + 1 ≤ fuel →
    placeOf fuel component = placeAt component := by
  intro fuel enough
  obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le enough
  induction extra with
  | zero => rfl
  | succ extra recurse =>
      rw [← Nat.add_assoc, ← (places_settle _).1 component (by omega), recurse (by omega)]

/-- **The outer place of a well-located block** is its place, when a component sits there. -/
theorem outerPlace_well {isLoc : Pattern → Prop} {outer count : Nat} {components : List Pattern}
    (well : WellLocated isLoc (.bvar outer) ⟨count, components⟩)
    (sits : ∃ component ∈ components, placeAt component = some (.bvar (outer + count))) {fuel : Nat}
    (enough : ∀ component ∈ components, 2 * size component + 2 ≤ fuel) :
    outerPlace fuel ⟨count, components⟩ = some (.bvar outer) := by
  obtain ⟨witness, witnessMember, witnessSits⟩ := sits
  obtain ⟨fuel, rfl⟩ : ∃ fuel', fuel = fuel' + 1 := ⟨fuel - 1, by have := enough _ witnessMember; omega⟩
  simp only [outerPlace]
  have settled : ∀ component ∈ components, placeOf fuel component = placeAt component :=
    fun component member => placeOf_eq_placeAt (by have := enough component member; omega)
  refine findSome?_eq_of_mem ⟨witness, witnessMember, ?_⟩ fun component member => ?_
  · rw [settled witness witnessMember, witnessSits, Option.bind_some]
    simp [lowerBy]
  · rw [settled component member]
    cases found : placeAt component with
    | none => exact .inl rfl
    | some at' =>
        rw [Option.bind_some]
        rcases well.placed component member at' found with same | ⟨index, below, rfl, -⟩
        · change at' = liftBVars 0 count (.bvar outer) at same
          subst same
          right
          simp [liftBVars, lowerBy]
        · change index < count at below
          left
          simp [lowerBy, show ¬ count ≤ index by omega]

/-- **A component using its block's place from outside sits there**: names are no locations, and blocks inside a
component use from outside only the component's place among the locations. -/
theorem WellLocated.uses_place {isLoc : Pattern → Prop} {outer count : Nat} {components : List Pattern}
    (well : WellLocated isLoc (.bvar outer) ⟨count, components⟩) :
    ∀ component ∈ components, FreeIn (outer + count) component →
      placeAt component = some (.bvar (outer + count)) := by
  have placeInside : insideLoc isLoc count components (.bvar (outer + count)) := by
    simp only [insideLoc, show ¬ outer + count < count by omega, if_false, show outer + count - count = outer by omega]
    exact well.placeIsLoc
  have notName : ∀ component ∈ components, ∀ name, nameOf component = some name →
      ¬ FreeIn (outer + count) name := by
    intro component member name isName free
    obtain ⟨isVar, apart⟩ := well.names component member name isName
    cases name with
    | bvar index =>
        cases free
        exact apart placeInside
    | _ => simp [isVariable] at isVar <;> cases free
  intro component member free
  cases well.kinds component member with
  | @marker markerLabel parent name index isMarker below =>
      change index < count at below
      obtain ⟨argument, inArguments, freeHere⟩ := Mettapedia.OSLF.MeTTaIL.CanonicalBags.freeIn_apply.mp free
      simp only [List.mem_cons, List.not_mem_nil, or_false] at inArguments
      rcases inArguments with isParent | isChild | isName
      · rw [isParent] at freeHere
        rcases well.placed _ member parent (placeAt_ofMarker isMarker _ _ _) with same | ⟨other, otherBelow, same, -⟩
        · change parent = liftBVars 0 count (.bvar outer) at same
          rw [placeAt_ofMarker isMarker, same]
          simp [liftBVars]
        · rw [same, freeIn_bvar] at freeHere
          change other < count at otherBelow
          omega
      · rw [isChild] at freeHere
        cases freeHere
        omega
      · rw [isName] at freeHere
        exact absurd freeHere (notName _ member _ (by simp [nameOf, isMarker]))
  | @capability label at' name continuation listed =>
      obtain ⟨argument, inArguments, freeHere⟩ := Mettapedia.OSLF.MeTTaIL.CanonicalBags.freeIn_apply.mp free
      simp only [List.mem_cons, List.not_mem_nil, or_false] at inArguments
      have placed := placeAt_capability listed at' name continuation
      rcases inArguments with isPlace | isName | isContinuation
      · rw [isPlace] at freeHere
        rcases well.placed _ member at' placed with same | ⟨other, otherBelow, same, -⟩
        · change at' = liftBVars 0 count (.bvar outer) at same
          rw [placed, same]
          simp [liftBVars]
        · rw [same, freeIn_bvar] at freeHere
          change other < count at otherBelow
          omega
      · rw [isName] at freeHere
        exact absurd freeHere (notName _ member _ (by
          simp only [nameOf]
          split_ifs with isMarker
          · exact absurd listed (not_capability_of_marker isMarker)
          · rfl))
      · rw [isContinuation] at freeHere
        have inner := match well with
          | .intro _ _ _ _ _ caps _ _ _ _ _ _ => caps _ member label at' name continuation rfl listed
        obtain ⟨innerComponent, innerMember, innerFree⟩ :=
          (Mettapedia.GSLT.LanguageDef.RestrictionBlocks.freeIn_decompose (block := locatedBlock) continuation _).mp
            freeHere
        rcases inner.freeIn_outer (insideLoc_locVariables isLoc count components) innerComponent innerMember _
            innerFree (Nat.le_add_left _ _) with same | apart
        · rw [placed, ← same]
          simp
        · exact absurd (by simpa using placeInside) apart
  | @replication argument =>
      obtain ⟨inner, inArguments, freeHere⟩ := Mettapedia.OSLF.MeTTaIL.CanonicalBags.freeIn_apply.mp free
      simp only [List.mem_cons, List.not_mem_nil, or_false] at inArguments
      subst inArguments
      obtain ⟨at', placed⟩ := Option.isSome_iff_exists.mp (well.repsPlaced _ member inner rfl)
      have innerWell := match well with
        | .intro _ _ _ _ _ _ reps _ _ _ _ _ => reps _ member inner at' rfl placed
      obtain ⟨innerComponent, innerMember, innerFree⟩ :=
        (Mettapedia.GSLT.LanguageDef.RestrictionBlocks.freeIn_decompose (block := locatedBlock) inner _).mp freeHere
      rcases innerWell.freeIn_outer (insideLoc_locVariables isLoc count components) innerComponent innerMember _
          innerFree (Nat.le_add_left _ _) with same | apart
      · rw [placed, ← same]
        simp
      · exact absurd (by simpa using placeInside) apart
  | @cap at' message continuation =>
      obtain ⟨argument, inArguments, freeHere⟩ := Mettapedia.OSLF.MeTTaIL.CanonicalBags.freeIn_apply.mp free
      simp only [List.mem_cons, List.not_mem_nil, or_false] at inArguments
      have placed := placeAt_cap at' message continuation
      rcases inArguments with isPlace | isMessage' | isContinuation
      · rw [isPlace] at freeHere
        rcases well.placed _ member at' placed with same | ⟨other, otherBelow, same, -⟩
        · change at' = liftBVars 0 count (.bvar outer) at same
          rw [placed, same]
          simp [liftBVars]
        · rw [same, freeIn_bvar] at freeHere
          change other < count at otherBelow
          omega
      · rw [isMessage'] at freeHere
        obtain ⟨isMsg, apart⟩ := well.messages _ member message (by simp [messageOf])
        exact absurd placeInside (apart _ (freeIn_messageVariables isMsg freeHere))
      · rw [isContinuation] at freeHere
        have inner := well.capConts _ member at' message continuation rfl
        obtain ⟨innerComponent, innerMember, innerFree⟩ :=
          (Mettapedia.GSLT.LanguageDef.RestrictionBlocks.freeIn_decompose (block := locatedBlock) continuation _).mp
            freeHere
        rcases inner.freeIn_outer (insideLoc_locVariables isLoc count components) innerComponent innerMember _
            innerFree (Nat.le_add_left _ _) with same | apart
        · rw [placed, ← same]
          simp
        · exact absurd (by simpa using placeInside) apart
  | @input label at' binder body listed =>
      obtain ⟨argument, inArguments, freeHere⟩ := Mettapedia.OSLF.MeTTaIL.CanonicalBags.freeIn_apply.mp free
      simp only [List.mem_cons, List.not_mem_nil, or_false] at inArguments
      have placed := placeAt_input listed at' (.lambda binder body)
      rcases inArguments with isPlace | isBody
      · rw [isPlace] at freeHere
        rcases well.placed _ member at' placed with same | ⟨other, otherBelow, same, -⟩
        · change at' = liftBVars 0 count (.bvar outer) at same
          rw [placed, same]
          simp [liftBVars]
        · rw [same, freeIn_bvar] at freeHere
          change other < count at otherBelow
          omega
      · rw [isBody] at freeHere
        have freeBody := Mettapedia.OSLF.MeTTaIL.CanonicalBags.freeIn_lambda.mp freeHere
        have inner := well.bodies _ member label at' binder body rfl listed
        obtain ⟨innerComponent, innerMember, innerFree⟩ :=
          (Mettapedia.GSLT.LanguageDef.RestrictionBlocks.freeIn_decompose (block := locatedBlock) body _).mp freeBody
        rcases inner.freeIn_outer (underName_locVariables _) innerComponent innerMember _ innerFree
            (Nat.le_add_left _ _) with same | apart
        · simp only [Nat.add_sub_cancel] at same
          rw [placed]
          cases at' with
          | bvar index =>
              simp only [liftBVars, Nat.zero_le, if_true, Pattern.bvar.injEq] at same
              simp only [Option.some.injEq, Pattern.bvar.injEq]
              omega
          | _ => simp [liftBVars] at same
        · exact absurd (by simpa [underName] using placeInside) apart
  | @output label at' message listed =>
      obtain ⟨argument, inArguments, freeHere⟩ := Mettapedia.OSLF.MeTTaIL.CanonicalBags.freeIn_apply.mp free
      simp only [List.mem_cons, List.not_mem_nil, or_false] at inArguments
      have placed := placeAt_output listed at' message
      rcases inArguments with isPlace | isMessage'
      · rw [isPlace] at freeHere
        rcases well.placed _ member at' placed with same | ⟨other, otherBelow, same, -⟩
        · change at' = liftBVars 0 count (.bvar outer) at same
          rw [placed, same]
          simp [liftBVars]
        · rw [same, freeIn_bvar] at freeHere
          change other < count at otherBelow
          omega
      · rw [isMessage'] at freeHere
        obtain ⟨isMsg, apart⟩ := well.messages _ member message (by simp [messageOf, listed])
        exact absurd placeInside (apart _ (freeIn_messageVariables isMsg freeHere))

/-- **A replication's place is its canonical argument's**: the canonical block uses the place from outside as the
argument's block does, so a component of it sits there. -/
theorem placeAt_replicated_canonical {isLoc : Pattern → Prop} {outer : Nat} {argument : Pattern}
    (placed : placeAt (.apply "LRep" [argument]) = some (.bvar outer))
    (normalWell : WellLocated isLoc (.bvar outer) (normal locatedRepBlock (decompose locatedBlock argument))) :
    placeAt (.apply "LRep" [canonicalOf locatedRepBlock argument]) = some (.bvar outer) := by
  have fresh : locatedRepBlock.replicate ∉ locatedRepBlock.emptyUnits := by decide
  have restrictFresh : locatedRepBlock.replicate ≠ locatedRepBlock.restrict := by decide
  set form := decompose locatedBlock argument with formIs
  set canonical := normal locatedRepBlock form with canonicalIs
  -- the argument's block uses its place from outside
  have outerIs : outerPlace (2 * size argument + 2) form = some (.bvar outer) := by
    have unfolded : placeAt (.apply "LRep" [argument]) = outerPlace (2 * size argument + 2) form := by
      simp only [placeAt, size, sizeList]
      rw [show 2 * (size argument + 0 + 1) + 1 = (2 * size argument + 2) + 1 by omega]
      simp [placeOf, formIs]
    rw [← unfolded, placed]
  have usesPlace : form.FreePast outer := by
    obtain ⟨count, components⟩ := form
    simp only [outerPlace] at outerIs
    obtain ⟨component, member, lowered⟩ := List.exists_of_findSome?_eq_some outerIs
    cases found : placeOf (2 * size argument + 1) component with
    | none => rw [found] at lowered; cases lowered
    | some at' =>
        rw [found, Option.bind_some] at lowered
        cases at' with
        | bvar index =>
            simp only [lowerBy] at lowered
            split_ifs at lowered with above
            simp only [Option.some.injEq, Pattern.bvar.injEq] at lowered
            refine ⟨component, member, ?_⟩
            simp only
            rw [show outer + count = index by omega]
            exact (freeIn_placeOf _).1 component index found
        | fvar _ => simp [lowerBy] at lowered
        | _ => simp [lowerBy] at lowered
  have canonicalUses : canonical.FreePast outer :=
    (freePast_normal_all fresh restrictFresh (decompose_atomic (base := locatedBlock) argument) outer).mpr usesPlace
  obtain ⟨witness, witnessMember, witnessFree⟩ := canonicalUses
  obtain ⟨canonicalCount, canonicalComponents⟩ := canonical
  have sits := normalWell.uses_place witness witnessMember witnessFree
  -- read the canonical argument's place
  have unfolded : placeAt (.apply "LRep" [canonicalOf locatedRepBlock argument]) =
      outerPlace (2 * size (canonicalOf locatedRepBlock argument) + 2) ⟨canonicalCount, canonicalComponents⟩ := by
    simp only [placeAt, size, sizeList]
    rw [show 2 * (size (canonicalOf locatedRepBlock argument) + 0 + 1) + 1 =
      (2 * size (canonicalOf locatedRepBlock argument) + 2) + 1 by omega]
    simp only [placeOf, if_true]
    rw [decompose_canonicalOf fresh restrictFresh, ← formIs, ← canonicalIs]
  rw [unfolded]
  refine outerPlace_well normalWell ⟨witness, witnessMember, sits⟩ fun component member => ?_
  have heavier := mass_le_size_toPattern (block := locatedBlock) (Prenex.mk canonicalCount canonicalComponents)
  have inside := size_le_sizeList member
  simp only [Prenex.mass] at heavier
  have canonicalIs' : canonicalOf locatedRepBlock argument =
      Prenex.toPattern locatedBlock ⟨canonicalCount, canonicalComponents⟩ := by
    simp only [canonicalOf, ← formIs]
    rw [← canonicalIs]
  rw [canonicalIs']
  omega

/-! ## Parts read canonically -/

open Mettapedia.GSLT.LanguageDef.RestrictionBlocks (recanon recanon_apply_other canonArgument normal_sound_at
  replicate_fill BaseContext decompose_sound)
open Mettapedia.Languages.ProcessCalculi.Ambient.Full (prefix_fill acap_fill input_fill)

/-- **A block inside a well-located block reads its parts canonically whole**: it is no variable, abstraction or
substitution, whose block would be a component of no kind. -/
theorem canonArgument_of_well {isLoc : Pattern → Prop} {place argument : Pattern}
    (well : WellLocated isLoc place (decompose locatedBlock argument)) (canonical : Pattern → Pattern) :
    canonArgument canonical argument = canonical argument := by
  have kindOf : decompose locatedBlock argument = Prenex.atom argument →
      ComponentKind (decompose locatedBlock argument).count argument := fun isAtom =>
    well.kinds argument (by rw [isAtom]; exact List.mem_singleton_self _)
  cases argument with
  | bvar index => exact absurd (kindOf (by simp [decompose])) (by intro kind; cases kind)
  | fvar name => exact absurd (kindOf (by simp [decompose])) (by intro kind; cases kind)
  | lambda binder body => exact absurd (kindOf (by simp [decompose])) (by intro kind; cases kind)
  | subst body replacement => exact absurd (kindOf (by simp [decompose])) (by intro kind; cases kind)
  | apply label arguments => rfl
  | multiLambda arity binders body => rfl
  | collection kind elements rest => rfl

theorem canonArgument_variable {pattern : Pattern} (isVar : isVariable pattern = true) (canonical : Pattern → Pattern) :
    canonArgument canonical pattern = pattern := by
  cases pattern <;> simp_all [isVariable, canonArgument]

/-- A marker's parts are variables, read as they are. -/
theorem recanon_marker {label : String} (isMarker : label ∈ markers) {parent child name : Pattern}
    (parentVar : isVariable parent = true) (childVar : isVariable child = true) (nameVar : isVariable name = true) :
    recanon locatedRepBlock (.apply label [parent, child, name]) = .apply label [parent, child, name] := by
  have notRestrict : label ≠ locatedRepBlock.restrict := by
    simp only [markers, List.mem_cons, List.not_mem_nil, or_false] at isMarker
    rcases isMarker with rfl | rfl <;> decide
  have notListed : label ∉ locatedRepBlock.multisets := by
    simp only [markers, List.mem_cons, List.not_mem_nil, or_false] at isMarker
    rcases isMarker with rfl | rfl <;> decide
  rw [recanon_apply_other (block := locatedRepBlock) notRestrict notListed]
  simp [canonArgument_variable parentVar, canonArgument_variable childVar, canonArgument_variable nameVar]

/-- A capability's continuation is read canonically. -/
theorem recanon_capability {label : String} (listed : label ∈ capabilities) {at' name continuation : Pattern}
    (atVar : isVariable at' = true) (nameVar : isVariable name = true)
    (whole : canonArgument (canonicalOf locatedRepBlock) continuation = canonicalOf locatedRepBlock continuation) :
    recanon locatedRepBlock (.apply label [at', name, continuation]) =
      .apply label [at', name, canonicalOf locatedRepBlock continuation] := by
  have notRestrict : label ≠ locatedRepBlock.restrict := by
    simp only [capabilities, List.mem_cons, List.not_mem_nil, or_false] at listed
    rcases listed with rfl | rfl | rfl <;> decide
  rw [recanon_apply_other (block := locatedRepBlock) notRestrict (by simp)]
  simp [canonArgument_variable atVar, canonArgument_variable nameVar, whole]

/-- **A message is its own canonical argument**: nothing inside it is a block. -/
theorem canonArgument_message : ∀ {message : Pattern}, isMessage message = true →
    canonArgument (canonicalOf locatedRepBlock) message = message
  | .bvar _, _ => rfl
  | .fvar _, _ => rfl
  | .apply label [], isMsg => by
      simp only [isMessage, beq_iff_eq] at isMsg
      subst isMsg
      have atomic : decompose locatedBlock (.apply "CapEps" []) = Prenex.atom (.apply "CapEps" []) :=
        Mettapedia.GSLT.LanguageDef.RestrictionBlocks.decompose_atom (by simp) (by simp) (by simp) (by simp)
      show canonicalOf locatedRepBlock (.apply "CapEps" []) = _
      rw [Mettapedia.GSLT.LanguageDef.RestrictionBlocks.canonicalOf_atom atomic,
        recanon_apply_other (block := locatedRepBlock) (by decide) (by simp)]
      rfl
  | .apply label [name], isMsg => by
      simp only [isMessage, Bool.and_eq_true, decide_eq_true_eq] at isMsg
      obtain ⟨listed, nameVar⟩ := isMsg
      simp only [List.mem_cons, List.not_mem_nil, or_false] at listed
      have atomic : decompose locatedBlock (.apply label [name]) = Prenex.atom (.apply label [name]) := by
        refine Mettapedia.GSLT.LanguageDef.RestrictionBlocks.decompose_atom ?_ ?_ (by simp) ?_ <;>
          rcases listed with rfl | rfl | rfl <;> simp
      have notRestrict : label ≠ locatedRepBlock.restrict := by
        rcases listed with rfl | rfl | rfl <;> decide
      show canonicalOf locatedRepBlock (.apply label [name]) = _
      rw [Mettapedia.GSLT.LanguageDef.RestrictionBlocks.canonicalOf_atom atomic,
        recanon_apply_other (block := locatedRepBlock) notRestrict (by simp)]
      simp [canonArgument_variable nameVar]
  | .apply label [first, second], isMsg => by
      simp only [isMessage, Bool.and_eq_true, beq_iff_eq] at isMsg
      obtain ⟨⟨rfl, firstMsg⟩, secondMsg⟩ := isMsg
      have atomic : decompose locatedBlock (.apply "CapPath" [first, second]) =
          Prenex.atom (.apply "CapPath" [first, second]) :=
        Mettapedia.GSLT.LanguageDef.RestrictionBlocks.decompose_atom (by simp) (by simp) (by simp) (by simp)
      show canonicalOf locatedRepBlock (.apply "CapPath" [first, second]) = _
      rw [Mettapedia.GSLT.LanguageDef.RestrictionBlocks.canonicalOf_atom atomic,
        recanon_apply_other (block := locatedRepBlock) (by decide) (by simp)]
      simp [canonArgument_message firstMsg, canonArgument_message secondMsg]
  | .apply _ (_ :: _ :: _ :: _), isMsg => by simp [isMessage] at isMsg
  | .lambda _ _, isMsg => by simp [isMessage] at isMsg
  | .multiLambda _ _ _, isMsg => by simp [isMessage] at isMsg
  | .subst _ _, isMsg => by simp [isMessage] at isMsg
  | .collection _ _ _, isMsg => by simp [isMessage] at isMsg

/-- A prefix's continuation is read canonically; its message is its own. -/
theorem recanon_cap {at' message continuation : Pattern} (atVar : isVariable at' = true)
    (messageIs : isMessage message = true)
    (whole : canonArgument (canonicalOf locatedRepBlock) continuation = canonicalOf locatedRepBlock continuation) :
    recanon locatedRepBlock (.apply "LCap" [at', message, continuation]) =
      .apply "LCap" [at', message, canonicalOf locatedRepBlock continuation] := by
  rw [recanon_apply_other (block := locatedRepBlock) (by decide) (by simp)]
  simp [canonArgument_variable atVar, canonArgument_message messageIs, whole]

/-- An input's body is read canonically, under its binder. -/
theorem recanon_input {label : String} (listed : label ∈ inputs) {at' : Pattern} {binder : Option String}
    {body : Pattern} (atVar : isVariable at' = true) :
    recanon locatedRepBlock (.apply label [at', .lambda binder body]) =
      .apply label [at', .lambda binder (canonicalOf locatedRepBlock body)] := by
  have notRestrict : label ≠ locatedRepBlock.restrict := by
    simp only [inputs, List.mem_cons, List.not_mem_nil, or_false] at listed
    rcases listed with rfl | rfl <;> decide
  rw [recanon_apply_other (block := locatedRepBlock) notRestrict (by simp)]
  simp only [List.map_cons, List.map_nil, canonArgument_variable atVar]
  rfl

/-- An output is its own canonical form. -/
theorem recanon_output {label : String} (listed : label ∈ outputs) {at' message : Pattern}
    (atVar : isVariable at' = true) (messageIs : isMessage message = true) :
    recanon locatedRepBlock (.apply label [at', message]) = .apply label [at', message] := by
  have notRestrict : label ≠ locatedRepBlock.restrict := by
    simp only [outputs, List.mem_cons, List.not_mem_nil, or_false] at listed
    rcases listed with rfl | rfl <;> decide
  rw [recanon_apply_other (block := locatedRepBlock) notRestrict (by simp)]
  simp [canonArgument_variable atVar, canonArgument_message messageIs]

/-- A replication's argument is read canonically. -/
theorem recanon_replicated {argument : Pattern}
    (whole : canonArgument (canonicalOf locatedRepBlock) argument = canonicalOf locatedRepBlock argument) :
    recanon locatedRepBlock (.apply "LRep" [argument]) = .apply "LRep" [canonicalOf locatedRepBlock argument] := by
  rw [recanon_apply_other (block := locatedRepBlock) (by decide) (by decide)]
  simp [whole]

/-- **The canonical parts of a component of a well-located block**: a marker and an output as they are; a capability,
a replication or a prefix with its block read canonically; an input with its body read canonically. -/
theorem WellLocated.recanon_shape {isLoc : Pattern → Prop} {place : Pattern} {count : Nat} {components : List Pattern}
    (well : WellLocated isLoc place ⟨count, components⟩) (locVariables : LocVariables isLoc) {component : Pattern}
    (member : component ∈ components) :
    recanon locatedRepBlock component = component ∨
      (∃ label at' name continuation, component = .apply label [at', name, continuation] ∧ label ∈ capabilities ∧
        recanon locatedRepBlock component = .apply label [at', name, canonicalOf locatedRepBlock continuation]) ∨
      (∃ argument, component = .apply "LRep" [argument] ∧
        recanon locatedRepBlock component = .apply "LRep" [canonicalOf locatedRepBlock argument]) ∨
      (∃ at' message continuation, component = .apply "LCap" [at', message, continuation] ∧
        recanon locatedRepBlock component = .apply "LCap" [at', message, canonicalOf locatedRepBlock continuation]) ∨
      (∃ label at' binder body, component = .apply label [at', .lambda binder body] ∧ label ∈ inputs ∧
        recanon locatedRepBlock component = .apply label [at', .lambda binder (canonicalOf locatedRepBlock body)]) := by
  have placeVar : ∀ at', placeAt component = some at' → isVariable at' = true := fun at' isPlaced =>
    insideLoc_locVariables isLoc count components at' (well.placeInside locVariables component member at' isPlaced)
  cases well.kinds component member with
  | @marker markerLabel parent name index isMarker below =>
      exact .inl (recanon_marker isMarker (placeVar parent (placeAt_ofMarker isMarker _ _ _)) rfl
        (well.names _ member name (by simp [nameOf, isMarker])).1)
  | @capability label at' name continuation listed =>
      have notMarker := not_marker_of_capability listed
      have inner := match well with
        | .intro _ _ _ _ _ caps _ _ _ _ _ _ => caps _ member label at' name continuation rfl listed
      exact .inr (.inl ⟨label, at', name, continuation, rfl, listed, recanon_capability listed
        (placeVar at' (placeAt_capability listed _ _ _))
        (well.names _ member name (by simp [nameOf, notMarker, listed])).1 (canonArgument_of_well inner _)⟩)
  | @replication argument =>
      obtain ⟨at', placed⟩ := Option.isSome_iff_exists.mp (well.repsPlaced _ member argument rfl)
      have inner := match well with
        | .intro _ _ _ _ _ _ reps _ _ _ _ _ => reps _ member argument at' rfl placed
      exact .inr (.inr (.inl ⟨argument, rfl, recanon_replicated (canonArgument_of_well inner _)⟩))
  | @cap at' message continuation =>
      have inner := well.capConts _ member at' message continuation rfl
      exact .inr (.inr (.inr (.inl ⟨at', message, continuation, rfl,
        recanon_cap (placeVar at' (placeAt_cap _ _ _)) (well.messages _ member message (by simp [messageOf])).1
          (canonArgument_of_well inner _)⟩)))
  | @input label at' binder body listed =>
      exact .inr (.inr (.inr (.inr ⟨label, at', binder, body, rfl, listed,
        recanon_input listed (placeVar at' (placeAt_input listed _ _))⟩)))
  | @output label at' message listed =>
      exact .inl (recanon_output listed (placeVar at' (placeAt_output listed _ _))
        (well.messages _ member message (by simp [messageOf, listed])).1)

/-- The weight of the blocks inside a component and of their canonical blocks. -/
def innerWeight : Pattern → Nat
  | .apply _ [_, _, continuation] => (decompose locatedBlock continuation).mass +
      (normal locatedRepBlock (decompose locatedBlock continuation)).mass
  | .apply _ [_, .lambda _ body] => (decompose locatedBlock body).mass +
      (normal locatedRepBlock (decompose locatedBlock body)).mass
  | .apply _ [argument] => (decompose locatedBlock argument).mass +
      (normal locatedRepBlock (decompose locatedBlock argument)).mass
  | _ => 0

/-- **Parts read canonically read back as the parts** and keep the block well-located, when the lighter blocks read
back as their canonical blocks. -/
theorem decode_recanon {bound : List TypeExpr} {isLoc : Pattern → Prop} {outer count : Nat}
    {components : List Pattern} (well : WellLocated isLoc (.bvar outer) ⟨count, components⟩)
    (locVariables : LocVariables isLoc) (context : BaseContext free bound)
    (members : Members locatedCalc locatedBlock free (List.replicate count nameType ++ bound) components)
    (normalBelow : NormalBelow free (Prenex.mk count components).mass) :
    WellLocated isLoc (.bvar outer) ⟨count, components.map (recanon locatedRepBlock)⟩ ∧
      Members locatedCalc locatedBlock free (List.replicate count nameType ++ bound)
        (components.map (recanon locatedRepBlock)) ∧
      ∀ fuel, 3 * (components.map innerWeight).sum + 2 * components.length + 6 ≤ fuel →
        ProcEquiv ambientCoreCalc ambientBlock free bound
          (Prenex.toPattern ambientBlock
            (decodeForm fuel (.bvar outer) ⟨count, components.map (recanon locatedRepBlock)⟩))
          (Prenex.toPattern ambientBlock (decodeForm fuel (.bvar outer) ⟨count, components⟩)) := by
  have signature : Mettapedia.GSLT.LanguageDef.RestrictionBlocks.BlockSignature locatedCalc locatedBlock :=
    Mettapedia.Languages.ProcessCalculi.Ambient.Located.locatedLanguage.toBlockSignature
  have fresh : locatedRepBlock.replicate ∉ locatedRepBlock.emptyUnits := by decide
  have restrictFresh : locatedRepBlock.replicate ≠ locatedRepBlock.restrict := by decide
  have innerContext := context.replicate count "Name"
  have insideVariables := insideLoc_locVariables isLoc count components
  set low := 3 * (components.map innerWeight).sum + 3 with lowIs
  -- the blocks inside components: well-located at the component's place, typed, lighter, read canonically
  have partFacts : ∀ component ∈ components, ∀ inner at', placeAt component = some at' →
      ((∃ label name, component = .apply label [at', name, inner] ∧ label ∈ capabilities) ∨
        component = .apply "LRep" [inner] ∨ (∃ message, component = .apply "LCap" [at', message, inner])) →
      (∃ index, at' = .bvar index) ∧ WellLocated (insideLoc isLoc count components) at' (decompose locatedBlock inner) ∧
        NormalFacts free (decompose locatedBlock inner) ∧
        HasType locatedCalc free (List.replicate count nameType ++ bound) inner procType ∧
        3 * innerWeight component + 3 ≤ low := by
    intro component member inner at' isPlaced shape
    have atBvar : ∃ index, at' = .bvar index := by
      rcases well.placed component member at' isPlaced with same | ⟨index, -, same, -⟩
      · exact ⟨outer + count, by rw [same]; simp [liftBVars]⟩
      · exact ⟨index, same⟩
    have weight : 3 * innerWeight component + 3 ≤ low := by
      have := List.le_sum_of_mem (List.mem_map_of_mem (f := innerWeight) member)
      omega
    have inComponents := size_le_sizeList member
    have sized : size inner < size component := by
      rcases shape with ⟨label, name, rfl, -⟩ | rfl | ⟨message, rfl⟩
      · simp only [size, sizeList]; omega
      · simp only [size, sizeList]; omega
      · simp only [size, sizeList]; omega
    have lighter : (decompose locatedBlock inner).mass < (Prenex.mk count components).mass := by
      have := mass_decompose (block := locatedBlock) inner
      have formMass : (Prenex.mk count components).mass = 2 * count + sizeList components := rfl
      omega
    rcases shape with ⟨label, name, rfl, listed⟩ | rfl | ⟨message, rfl⟩
    · have innerWell := match well with
        | .intro _ _ _ _ _ caps _ _ _ _ _ _ => caps _ member label at' name inner rfl listed
      rcases triple_inv (members _ member) with ⟨isMarker, -⟩ | ⟨-, -, innerTyped⟩ | ⟨rfl, -, -⟩
      · exact absurd listed (not_capability_of_marker isMarker)
      · exact ⟨atBvar, innerWell, normalBelow _ lighter, innerTyped, weight⟩
      · simp [capabilities] at listed
    · have innerWell := match well with
        | .intro _ _ _ _ _ _ reps _ _ _ _ _ => reps _ member inner at' rfl isPlaced
      exact ⟨atBvar, innerWell, normalBelow _ lighter, rep_inv (members _ member), weight⟩
    · have innerWell := well.capConts _ member at' message inner rfl
      rcases triple_inv (members _ member) with ⟨isMarker, -⟩ | ⟨listed, -, -⟩ | ⟨-, -, innerTyped⟩
      · simp [markers] at isMarker
      · simp [capabilities] at listed
      · exact ⟨atBvar, innerWell, normalBelow _ lighter, innerTyped, weight⟩
  -- the bodies of inputs: well-located at the input's place under its binder, typed there, lighter
  have bodyFacts : ∀ component ∈ components, ∀ label at' binder body,
      component = .apply label [at', .lambda binder body] → label ∈ inputs →
      (∃ index, at' = .bvar index) ∧
        WellLocated (underName (insideLoc isLoc count components)) (liftBVars 0 1 at') (decompose locatedBlock body) ∧
        NormalFacts free (decompose locatedBlock body) ∧
        (∃ sort, (label, sort) ∈ [("LInName", "Name"), ("LInCap", "Cap")] ∧ binder = none ∧
          HasType locatedCalc free (.base sort :: (List.replicate count nameType ++ bound)) body procType) ∧
        3 * innerWeight component + 3 ≤ low := by
    intro component member label at' binder body isInput listed
    have isPlaced : placeAt component = some at' := by rw [isInput]; exact placeAt_input listed _ _
    have atBvar : ∃ index, at' = .bvar index := by
      rcases well.placed component member at' isPlaced with same | ⟨index, -, same, -⟩
      · exact ⟨outer + count, by rw [same]; simp [liftBVars]⟩
      · exact ⟨index, same⟩
    have weight : 3 * innerWeight component + 3 ≤ low := by
      have := List.le_sum_of_mem (List.mem_map_of_mem (f := innerWeight) member)
      omega
    have inComponents := size_le_sizeList member
    have sized : size body < size component := by
      rw [isInput]; simp only [size, sizeList]; omega
    have lighter : (decompose locatedBlock body).mass < (Prenex.mk count components).mass := by
      have := mass_decompose (block := locatedBlock) body
      have formMass : (Prenex.mk count components).mass = 2 * count + sizeList components := rfl
      omega
    have bodyWell := well.bodies component member label at' binder body isInput listed
    subst isInput
    obtain ⟨-, ⟨sort, body', sorted, same, bodyTyped⟩ | ⟨sort, sorted, -⟩⟩ := pair_inv (members _ member)
    · simp only [Pattern.lambda.injEq] at same
      obtain ⟨rfl, rfl⟩ := same
      exact ⟨atBvar, bodyWell, normalBelow _ lighter, ⟨sort, sorted, rfl, bodyTyped⟩, weight⟩
    · exfalso
      apply not_output_of_input listed
      simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at sorted
      rcases sorted with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> simp
  -- a component read canonically keeps its place, its location, its name, its kind and its message
  have facts : ∀ component ∈ components,
      placeAt (recanon locatedRepBlock component) = placeAt component ∧
      childOf (recanon locatedRepBlock component) = childOf component ∧
      nameOf (recanon locatedRepBlock component) = nameOf component ∧
      ComponentKind count (recanon locatedRepBlock component) ∧
      messageOf (recanon locatedRepBlock component) = messageOf component := by
    intro component member
    rcases well.recanon_shape locVariables member with same | ⟨label, at', name, inner, rfl, listed, same⟩ |
        ⟨inner, rfl, same⟩ | ⟨at', message, inner, rfl, same⟩ | ⟨label, at', binder, body, rfl, listed, same⟩
    · rw [same]; exact ⟨rfl, rfl, rfl, well.kinds component member, rfl⟩
    · have notMarker := not_marker_of_capability listed
      have notCap : label ≠ "LCap" := by rintro rfl; simp [capabilities] at listed
      rw [same]
      refine ⟨by rw [placeAt_capability listed, placeAt_capability listed], by simp [childOf, notMarker],
        by simp [nameOf, notMarker, listed], .capability listed, by simp [messageOf, notCap]⟩
    · rw [same]
      obtain ⟨at', placed⟩ := Option.isSome_iff_exists.mp (well.repsPlaced _ member inner rfl)
      obtain ⟨⟨index, rfl⟩, innerWell, innerNormal, innerTyped, -⟩ :=
        partFacts _ member inner at' placed (.inr (.inl rfl))
      obtain ⟨innerMembers, -⟩ := decompose_sound (language := locatedCalc) (block := locatedBlock) innerTyped
      have normalWell := (innerNormal innerWell insideVariables innerContext innerMembers).1
      exact ⟨by rw [placed]; exact placeAt_replicated_canonical placed normalWell, by simp [childOf],
        by simp [nameOf], .replication, by simp [messageOf]⟩
    · rw [same]
      exact ⟨by rw [placeAt_cap, placeAt_cap], by simp [childOf, markers], by simp [nameOf, markers, capabilities],
        .cap, by simp [messageOf]⟩
    · rw [same]
      exact ⟨by rw [placeAt_input listed, placeAt_input listed], by simp [childOf], by simp [nameOf], .input listed,
        by simp [messageOf, not_output_of_input listed]⟩
  have recanonMember : ∀ {component}, component ∈ components →
      recanon locatedRepBlock component ∈ components.map (recanon locatedRepBlock) :=
    fun member => List.mem_map.mpr ⟨_, member, rfl⟩
  have markedSame : ∀ index, Marked (components.map (recanon locatedRepBlock)) index ↔ Marked components index := by
    intro index
    constructor
    · rintro ⟨marker, member, isChild⟩
      obtain ⟨original, inComponents, rfl⟩ := List.mem_map.mp member
      exact ⟨original, inComponents, by rw [← (facts original inComponents).2.1]; exact isChild⟩
    · rintro ⟨marker, member, isChild⟩
      exact ⟨_, recanonMember member, by rw [(facts marker member).2.1]; exact isChild⟩
  have insideSame : insideLoc isLoc count (components.map (recanon locatedRepBlock)) =
      insideLoc isLoc count components := by
    funext pattern
    apply propext
    cases pattern with
    | bvar index =>
        simp only [insideLoc]
        split_ifs
        · exact markedSame index
        · exact Iff.rfl
    | _ => exact Iff.rfl
  refine ⟨?_, ?_, ?_⟩
  · -- well-located
    refine .intro well.placeIsLoc (fun component member => ?_) (fun component member at' isPlaced => ?_)
      (fun index => ?_) (fun component member name isName => ?_) ?_ ?_ (fun component member argument isRep => ?_) ?_
      (fun component member message isMsgOf => ?_) ?_ ?_
    · obtain ⟨original, inComponents, rfl⟩ := List.mem_map.mp member
      exact (facts original inComponents).2.2.2.1
    · obtain ⟨original, inComponents, rfl⟩ := List.mem_map.mp member
      rw [(facts original inComponents).1] at isPlaced
      rcases well.placed original inComponents at' isPlaced with same | ⟨index, below, same, isMarked⟩
      · exact .inl same
      · exact .inr ⟨index, below, same, (markedSame index).mpr isMarked⟩
    · have whole := well.unique index
      simp only at whole ⊢
      rw [List.filter_map, List.length_map]
      refine le_of_eq_of_le ?_ whole
      congr 1
      exact List.filter_congr fun component member => by simp [Function.comp, (facts component member).2.1]
    · obtain ⟨original, inComponents, rfl⟩ := List.mem_map.mp member
      rw [(facts original inComponents).2.2.1] at isName
      rw [insideSame]
      exact well.names original inComponents name isName
    · intro component member label at' name continuation isCap listed
      obtain ⟨original, inComponents, rfl⟩ := List.mem_map.mp member
      rw [insideSame]
      rcases well.recanon_shape locVariables inComponents with same | ⟨label', at'', name', inner, rfl, listed', same⟩ |
          ⟨inner, rfl, same⟩ | ⟨at'', message', inner, rfl, same⟩ | ⟨label', at'', binder', body', rfl, listed', same⟩
      · rw [same] at isCap
        subst isCap
        exact match well with | .intro _ _ _ _ _ caps _ _ _ _ _ _ => caps _ inComponents label at' name continuation rfl listed
      · rw [same] at isCap
        simp only [Pattern.apply.injEq, List.cons.injEq, and_true] at isCap
        obtain ⟨rfl, rfl, rfl, rfl⟩ := isCap
        obtain ⟨⟨index, rfl⟩, innerWell, innerNormal, innerTyped, -⟩ :=
          partFacts _ inComponents inner at'' (placeAt_capability listed' _ _ _) (.inl ⟨label', name', rfl, listed'⟩)
        obtain ⟨innerMembers, -⟩ := decompose_sound (language := locatedCalc) (block := locatedBlock) innerTyped
        rw [decompose_canonicalOf fresh restrictFresh]
        exact (innerNormal innerWell insideVariables innerContext innerMembers).1
      · rw [same] at isCap
        cases isCap
      · rw [same] at isCap
        simp only [Pattern.apply.injEq] at isCap
        obtain ⟨rfl, -⟩ := isCap
        simp [capabilities] at listed
      · rw [same] at isCap
        cases isCap
    · intro component member argument at' isRep isPlaced
      obtain ⟨original, inComponents, rfl⟩ := List.mem_map.mp member
      rw [insideSame]
      have originalPlaced := isPlaced
      rw [(facts original inComponents).1] at originalPlaced
      rcases well.recanon_shape locVariables inComponents with same | ⟨label', at'', name', inner, rfl, listed', same⟩ |
          ⟨inner, rfl, same⟩ | ⟨at'', message', inner, rfl, same⟩ | ⟨label', at'', binder', body', rfl, listed', same⟩
      · rw [same] at isRep
        subst isRep
        exact match well with | .intro _ _ _ _ _ _ reps _ _ _ _ _ => reps _ inComponents argument at' rfl originalPlaced
      · rw [same] at isRep
        cases isRep
      · rw [same] at isRep
        simp only [Pattern.apply.injEq, List.cons.injEq, and_true, true_and] at isRep
        subst isRep
        obtain ⟨⟨index, rfl⟩, innerWell, innerNormal, innerTyped, -⟩ :=
          partFacts _ inComponents inner at' originalPlaced (.inr (.inl rfl))
        obtain ⟨innerMembers, -⟩ := decompose_sound (language := locatedCalc) (block := locatedBlock) innerTyped
        rw [decompose_canonicalOf fresh restrictFresh]
        exact (innerNormal innerWell insideVariables innerContext innerMembers).1
      · rw [same] at isRep
        simp at isRep
      · rw [same] at isRep
        cases isRep
    · obtain ⟨original, inComponents, rfl⟩ := List.mem_map.mp member
      rw [(facts original inComponents).1]
      rcases well.recanon_shape locVariables inComponents with same | ⟨label', at'', name', inner, rfl, listed', same⟩ |
          ⟨inner, rfl, same⟩ | ⟨at'', message', inner, rfl, same⟩ | ⟨label', at'', binder', body', rfl, listed', same⟩
      · rw [same] at isRep
        exact well.repsPlaced original inComponents argument isRep
      · rw [same] at isRep
        cases isRep
      · exact well.repsPlaced _ inComponents inner rfl
      · rw [same] at isRep
        simp at isRep
      · rw [same] at isRep
        cases isRep
    · obtain ⟨depth, grows⟩ := well.nested
      refine ⟨depth, fun component member index child below childBelow isPlaced isChild => ?_⟩
      obtain ⟨original, inComponents, rfl⟩ := List.mem_map.mp member
      rw [(facts original inComponents).1] at isPlaced
      rw [(facts original inComponents).2.1] at isChild
      exact grows original inComponents index child below childBelow isPlaced isChild
    · obtain ⟨original, inComponents, rfl⟩ := List.mem_map.mp member
      rw [(facts original inComponents).2.2.2.2] at isMsgOf
      rw [insideSame]
      exact well.messages original inComponents message isMsgOf
    · intro component member at' message continuation isCapComponent
      obtain ⟨original, inComponents, rfl⟩ := List.mem_map.mp member
      rw [insideSame]
      rcases well.recanon_shape locVariables inComponents with same | ⟨label', at'', name', inner, rfl, listed', same⟩ |
          ⟨inner, rfl, same⟩ | ⟨at'', message', inner, rfl, same⟩ | ⟨label', at'', binder', body', rfl, listed', same⟩
      · rw [same] at isCapComponent
        subst isCapComponent
        exact well.capConts _ inComponents at' message continuation rfl
      · rw [same] at isCapComponent
        simp only [Pattern.apply.injEq] at isCapComponent
        obtain ⟨rfl, -⟩ := isCapComponent
        simp [capabilities] at listed'
      · rw [same] at isCapComponent
        simp at isCapComponent
      · rw [same] at isCapComponent
        simp only [Pattern.apply.injEq, List.cons.injEq, and_true, true_and] at isCapComponent
        obtain ⟨rfl, rfl, rfl⟩ := isCapComponent
        obtain ⟨⟨index, rfl⟩, innerWell, innerNormal, innerTyped, -⟩ :=
          partFacts _ inComponents inner _ (placeAt_cap _ _ _) (.inr (.inr ⟨message', rfl⟩))
        obtain ⟨innerMembers, -⟩ := decompose_sound (language := locatedCalc) (block := locatedBlock) innerTyped
        rw [decompose_canonicalOf fresh restrictFresh]
        exact (innerNormal innerWell insideVariables innerContext innerMembers).1
      · rw [same] at isCapComponent
        cases isCapComponent
    · intro component member label at' binder body isInput listed
      obtain ⟨original, inComponents, rfl⟩ := List.mem_map.mp member
      rw [insideSame]
      rcases well.recanon_shape locVariables inComponents with same | ⟨label', at'', name', inner, rfl, listed', same⟩ |
          ⟨inner, rfl, same⟩ | ⟨at'', message', inner, rfl, same⟩ | ⟨label', at'', binder', body', rfl, listed', same⟩
      · rw [same] at isInput
        subst isInput
        exact well.bodies _ inComponents label at' binder body rfl listed
      · rw [same] at isInput
        cases isInput
      · rw [same] at isInput
        cases isInput
      · rw [same] at isInput
        cases isInput
      · rw [same] at isInput
        simp only [Pattern.apply.injEq, List.cons.injEq, Pattern.lambda.injEq, and_true] at isInput
        obtain ⟨rfl, rfl, rfl, rfl⟩ := isInput
        obtain ⟨⟨index, rfl⟩, bodyWell, bodyNormal, ⟨sort, -, -, bodyTyped⟩, -⟩ :=
          bodyFacts _ inComponents _ _ _ _ rfl listed'
        obtain ⟨bodyMembers, -⟩ := decompose_sound (language := locatedCalc) (block := locatedBlock) bodyTyped
        have placeIs : liftBVars 0 1 (Pattern.bvar index) = .bvar (index + 1) := by simp [liftBVars]
        rw [placeIs] at bodyWell ⊢
        rw [decompose_canonicalOf fresh restrictFresh]
        exact (bodyNormal bodyWell (underName_locVariables _) (innerContext.cons sort) bodyMembers).1
  · -- typed
    intro element member
    obtain ⟨original, inComponents, rfl⟩ := List.mem_map.mp member
    exact ((normal_sound_at (language := locatedCalc) (block := locatedRepBlock)
      (3 * size original + 2)).2.1 innerContext (members original inComponents)).1
  · -- read back equivalently
    intro fuel enough
    obtain ⟨fuel, rfl⟩ : ∃ fuel', fuel = fuel' + 1 := ⟨fuel - 1, by omega⟩
    simp only [decodeForm, Prenex.toPattern]
    refine restricts_congr (language := ambientCoreCalc) (block := ambientBlock) count ?_
    have recanonMembers : Members locatedCalc locatedBlock free (List.replicate count nameType ++ bound)
        (components.map (recanon locatedRepBlock)) := by
      intro element member
      obtain ⟨original, inComponents, rfl⟩ := List.mem_map.mp member
      exact ((normal_sound_at (language := locatedCalc) (block := locatedRepBlock)
        (3 * size original + 2)).2.1 innerContext (members original inComponents)).1
    refine readPlaced_map_from (low := low) fuel _ (by omega) members recanonMembers
      (fun component member => (facts component member).1) ?_
    intro component member fuel' floor place' first second isPlaced firstMembers secondMembers children
    have placed : placeAt component = some place' := by simpa [placedAt] using isPlaced
    rcases well.recanon_shape locVariables member with same | ⟨label, at', name, inner, rfl, listed, same⟩ |
        ⟨inner, rfl, same⟩ | ⟨at', message, inner, rfl, same⟩ | ⟨label, at', binder, body, rfl, listed, same⟩
    · rw [same]
      exact readComponent_equivalent (members component member) children
    · rw [same]
      have notMarker := not_marker_of_capability listed
      rw [placeAt_capability listed, Option.some.injEq] at placed
      subst placed
      obtain ⟨⟨index, rfl⟩, innerWell, innerNormal, innerTyped, weight⟩ :=
        partFacts _ member inner _ (placeAt_capability listed _ _ _) (.inl ⟨label, name, rfl, listed⟩)
      obtain ⟨innerMembers, -⟩ := decompose_sound (language := locatedCalc) (block := locatedBlock) innerTyped
      have nameVar := (well.names _ member name (by simp [nameOf, notMarker, listed])).1
      have nameTyped : HasType ambientCoreCalc free (List.replicate count nameType ++ bound) name nameType := by
        rcases triple_inv (members _ member) with ⟨isMarker, -⟩ | ⟨-, nameTyped, -⟩ | ⟨rfl, -, -⟩
        · exact absurd listed (not_capability_of_marker isMarker)
        · exact variable_typed nameTyped nameVar
        · simp [capabilities] at listed
      simp only [innerWeight] at weight
      simp only [readComponent, if_neg notMarker, if_pos listed, if_pos nameVar]
      rw [decompose_canonicalOf fresh restrictFresh]
      exact prefix_fill (ambientCapability_mem listed) nameTyped
        ((innerNormal innerWell insideVariables innerContext innerMembers).2 fuel' (by omega) (by omega))
    · rw [same]
      obtain ⟨⟨index, rfl⟩, innerWell, innerNormal, innerTyped, weight⟩ :=
        partFacts _ member inner _ placed (.inr (.inl rfl))
      obtain ⟨innerMembers, -⟩ := decompose_sound (language := locatedCalc) (block := locatedBlock) innerTyped
      simp only [innerWeight] at weight
      simp only [readComponent, if_true]
      rw [decompose_canonicalOf fresh restrictFresh]
      exact replicate_fill (language := ambientCoreCalc) (block := ambientRepBlock)
        ((innerNormal innerWell insideVariables innerContext innerMembers).2 fuel' (by omega) (by omega))
    · rw [same]
      rw [placeAt_cap, Option.some.injEq] at placed
      subst placed
      obtain ⟨⟨index, rfl⟩, innerWell, innerNormal, innerTyped, weight⟩ :=
        partFacts _ member inner _ (placeAt_cap _ _ _) (.inr (.inr ⟨message, rfl⟩))
      obtain ⟨innerMembers, -⟩ := decompose_sound (language := locatedCalc) (block := locatedBlock) innerTyped
      have messageIs := (well.messages _ member message (by simp [messageOf])).1
      have messageTyped : HasType ambientCoreCalc free (List.replicate count nameType ++ bound) message capType := by
        rcases triple_inv (members _ member) with ⟨isMarker, -⟩ | ⟨listed, -, -⟩ | ⟨-, typed, -⟩
        · simp [markers] at isMarker
        · simp [capabilities] at listed
        · exact message_typed typed messageIs
      simp only [innerWeight] at weight
      rw [readComponent_cap, readComponent_cap, if_pos messageIs, if_pos messageIs]
      simp only [decodeAt]
      rw [decompose_canonicalOf fresh restrictFresh]
      exact acap_fill messageTyped
        ((innerNormal innerWell insideVariables innerContext innerMembers).2 fuel' (by omega) (by omega))
    · rw [same]
      rw [placeAt_input listed, Option.some.injEq] at placed
      subst placed
      obtain ⟨⟨index, rfl⟩, bodyWell, bodyNormal, ⟨sort, sorted, rfl, bodyTyped⟩, weight⟩ :=
        bodyFacts _ member _ _ _ _ rfl listed
      obtain ⟨bodyMembers, -⟩ := decompose_sound (language := locatedCalc) (block := locatedBlock) bodyTyped
      simp only [innerWeight] at weight
      rw [readComponent_input listed, readComponent_input listed]
      simp only [decodeAt]
      rw [decompose_canonicalOf fresh restrictFresh]
      have placeIs : liftBVars 0 1 (Pattern.bvar index) = .bvar (index + 1) := by simp [liftBVars]
      rw [placeIs] at bodyWell ⊢
      exact input_fill (ambientInput_listed sorted)
        ((bodyNormal bodyWell (underName_locVariables _) (innerContext.cons sort) bodyMembers).2 fuel' (by omega)
          (by omega))

/-! ## The canonical block -/

open Mettapedia.GSLT.LanguageDef.RestrictionBlocks (absorbOnce absorbRounds absorb normal_eq_reading least_reading_mem
  readingsR readingOrders_isOrder sortComponents prune_sound IsOrder inverse inverse_isOrder permute_inverse
  permute_injective permute_lt permute_of_ge orders_reorders orders_complete block_reorder_equivalent rename rename_comp
  rename_id sizeList_perm sizeList_append sizeList_map_rename mentions mentions_iff BlockSignature)

theorem NormalBelow.mono {weight smaller : Nat} (below : NormalBelow free weight) (lighter : smaller ≤ weight) :
    NormalBelow free smaller := fun form light => below form (by omega)

/-- **One absorption reads back as nothing**, and keeps the block well-located, typed, no heavier. -/
theorem decode_absorbOnce {bound : List TypeExpr} {isLoc : Pattern → Prop} {outer count : Nat}
    {components : List Pattern} {next : Prenex}
    (well : WellLocated isLoc (.bvar outer) ⟨count, components⟩) (locVariables : LocVariables isLoc)
    (context : BaseContext free bound)
    (members : Members locatedCalc locatedBlock free (List.replicate count nameType ++ bound) components)
    (absorbed : absorbOnce locatedRepBlock (canonicalOf locatedRepBlock) ⟨count, components⟩ = some next)
    (normalBelow : NormalBelow free (Prenex.mk count components).mass) :
    next.count = count ∧ next.mass ≤ (Prenex.mk count components).mass ∧
      WellLocated isLoc (.bvar outer) next ∧
      Members locatedCalc locatedBlock free (List.replicate count nameType ++ bound) next.components ∧
      ∃ least, ∀ fuel, least ≤ fuel → ProcEquiv ambientCoreCalc ambientBlock free bound
        (Prenex.toPattern ambientBlock (decodeForm fuel (.bvar outer) ⟨count, components⟩))
        (Prenex.toPattern ambientBlock (decodeForm fuel (.bvar outer) next)) := by
  obtain ⟨argument, group, kept, repMember, repKept, split, apart, nodup, inside, allowedOnly, covers, covered, copied,
    rfl⟩ := absorbOnce_shape absorbed
  obtain ⟨keptWell, decoded⟩ := decode_absorb_step well locVariables context members repMember repKept split apart
    nodup inside allowedOnly covers covered copied normalBelow
  refine ⟨rfl, ?_, keptWell,
    fun element member => members element (split.symm.subset (List.mem_append_right _ member)), decoded⟩
  have weights := sizeList_perm split
  rw [sizeList_append] at weights
  simp only [Prenex.mass]
  omega

/-- **Absorption in rounds reads back as nothing**, and keeps the block well-located, typed, no heavier. -/
theorem decode_absorbRounds {bound : List TypeExpr} {isLoc : Pattern → Prop} {outer : Nat}
    (locVariables : LocVariables isLoc) (context : BaseContext free bound) :
    ∀ (rounds : Nat) {form : Prenex}, WellLocated isLoc (.bvar outer) form →
      Members locatedCalc locatedBlock free (List.replicate form.count nameType ++ bound) form.components →
      NormalBelow free form.mass →
      (absorbRounds locatedRepBlock (canonicalOf locatedRepBlock) rounds form).count = form.count ∧
      (absorbRounds locatedRepBlock (canonicalOf locatedRepBlock) rounds form).mass ≤ form.mass ∧
      WellLocated isLoc (.bvar outer) (absorbRounds locatedRepBlock (canonicalOf locatedRepBlock) rounds form) ∧
      Members locatedCalc locatedBlock free (List.replicate form.count nameType ++ bound)
        (absorbRounds locatedRepBlock (canonicalOf locatedRepBlock) rounds form).components ∧
      ∃ least, ∀ fuel, least ≤ fuel → ProcEquiv ambientCoreCalc ambientBlock free bound
        (Prenex.toPattern ambientBlock (decodeForm fuel (.bvar outer) form))
        (Prenex.toPattern ambientBlock
          (decodeForm fuel (.bvar outer) (absorbRounds locatedRepBlock (canonicalOf locatedRepBlock) rounds form)))
  | 0, form, well, members, _ => ⟨rfl, le_rfl, well, members, 0, fun _ _ => .refl _⟩
  | rounds + 1, form, well, members, normalBelow => by
      unfold absorbRounds
      split
      · exact ⟨rfl, le_rfl, well, members, 0, fun _ _ => .refl _⟩
      · rename_i next absorbed
        obtain ⟨count, components⟩ := form
        obtain ⟨countSame, lighter, nextWell, nextMembers, firstLeast, first⟩ :=
          decode_absorbOnce well locVariables context members absorbed normalBelow
        obtain ⟨restCount, restLighter, restWell, restMembers, restLeast, rest⟩ :=
          decode_absorbRounds locVariables context rounds nextWell (by rw [countSame]; exact nextMembers)
            (normalBelow.mono lighter)
        refine ⟨by rw [restCount, countSame], le_trans restLighter lighter, restWell,
          by rw [countSame] at restMembers; exact restMembers, firstLeast + restLeast, fun fuel enough => ?_⟩
        exact .trans _ _ _ (first fuel (by omega)) (rest fuel (by omega))

/-- **A block with its unused restrictions dropped stays well-located.** -/
theorem WellLocated.prune {isLoc : Pattern → Prop} {place : Pattern} {form : Prenex}
    (well : WellLocated isLoc place form) (locVariables : LocVariables isLoc) :
    WellLocated isLoc place form.prune := by
  obtain ⟨count, components⟩ := form
  set kept := (List.range count).filter fun index => components.any (mentions index) with keptIs
  have nodup : kept.Nodup := List.nodup_range.filter _
  have inside : ∀ index ∈ kept, index < count := fun index member => List.mem_range.mp (List.mem_filter.mp member).1
  have uses : ∀ component ∈ components, ∀ index, FreeIn index component → index < count → index ∈ kept :=
    fun component member index free below => List.mem_filter.mpr ⟨List.mem_range.mpr below,
      List.any_eq_true.mpr ⟨component, member, (mentions_iff component index).mpr free⟩⟩
  simp only [Prenex.prune, ← keptIs]
  refine WellLocated.comap (relabel := ungroup count kept) (ungroup_injective nodup inside)
    (fun index below => by
      simp only [ungroup, below, if_true]
      rw [List.getD_eq_getElem _ _ below]
      exact inside _ (List.getElem_mem below))
    (fun offset => by simp only [ungroup]; split_ifs <;> omega) ?_ locVariables
  rw [ungroup_restores inside uses]
  exact well

/-- **A well-located block's canonical block is well-located and reads back as the block**: its copies absorbed, its
unused restrictions dropped, its restrictions reordered, its components' parts read canonically, sorted, one of each
replication kept. -/
theorem decode_normal (form : Prenex) : NormalFacts free form := by
  suffices all : ∀ weight, ∀ form : Prenex, form.mass < weight → NormalFacts free form from
    fun {_ _ _} well locVariables context members => all _ form (Nat.lt_succ_self _) well locVariables context members
  intro weight
  induction weight with
  | zero => intro form light; omega
  | succ weight recurse =>
      intro form light
      have normalBelow : NormalBelow free form.mass := fun lighter lighterMass => recurse lighter (by omega)
      intro isLoc outer bound well locVariables context members
      have signature : BlockSignature locatedCalc locatedBlock :=
        Mettapedia.Languages.ProcessCalculi.Ambient.Located.locatedLanguage.toBlockSignature
      obtain ⟨count, components⟩ := form
      -- absorb
      obtain ⟨roundsCount, roundsLighter, roundsWell, roundsMembers, roundsLeast, roundsDecode⟩ :=
        decode_absorbRounds locVariables context components.length well members normalBelow
      set absorbed := absorbRounds locatedRepBlock (canonicalOf locatedRepBlock) components.length
        ⟨count, components⟩ with absorbedIs
      -- prune
      have absorbedMembers : Members locatedCalc locatedBlock free
          (List.replicate absorbed.count nameType ++ bound) absorbed.components := by
        rw [roundsCount]; exact roundsMembers
      have prunedWell := roundsWell.prune locVariables
      have prunedMembers := (prune_sound (language := locatedCalc) (block := locatedRepBlock) absorbedMembers).1
      set pruned := absorbed.prune with prunedIs
      have prunedLighter : pruned.mass ≤ absorbed.mass := by
        obtain ⟨absorbedCount, absorbedComponents⟩ := absorbed
        simp only [prunedIs, Prenex.prune, Prenex.mass, sizeList_map_rename]
        have : ((List.range absorbedCount).filter fun index => absorbedComponents.any (mentions index)).length ≤
            absorbedCount := by
          have := List.length_filter_le (fun index => absorbedComponents.any (mentions index)) (List.range absorbedCount)
          simpa using this
        omega
      -- reorder
      obtain ⟨order, inOrders, leastIs⟩ := least_reading_mem (block := locatedRepBlock) pruned
      have isOrder : IsOrder pruned.count order := readingOrders_isOrder inOrders
      set reordered := pruned.components.map (rename (Prenex.permute pruned.count order)) with reorderedIs
      have reorderedWell : WellLocated isLoc (.bvar outer) ⟨pruned.count, reordered⟩ := by
        refine WellLocated.comap (relabel := Prenex.permute pruned.count (inverse pruned.count order))
          (permute_injective (inverse_isOrder isOrder)) (fun index below => permute_lt (inverse_isOrder isOrder) below)
          (fun offset => permute_of_ge _ (by omega)) ?_ locVariables
        rw [reorderedIs, List.map_map]
        have back : (rename (Prenex.permute pruned.count (inverse pruned.count order)) ∘
            rename (Prenex.permute pruned.count order)) = id := by
          funext pattern
          simp only [Function.comp, id, rename_comp, permute_inverse isOrder, rename_id]
        rw [back, List.map_id]
        exact prunedWell
      obtain ⟨reorderedMembers, -⟩ := block_reorder_equivalent (language := locatedCalc) (block := locatedBlock)
        (bound := bound) (orders_reorders (List.range pruned.count) order (orders_complete _ _ isOrder)) prunedMembers
      have reorderedLighter : (Prenex.mk pruned.count reordered).mass ≤ (Prenex.mk count components).mass := by
        have same : (Prenex.mk pruned.count reordered).mass = pruned.mass := by
          simp only [Prenex.mass, reorderedIs, sizeList_map_rename]
        have : absorbed.mass ≤ (Prenex.mk count components).mass := roundsLighter
        omega
      -- read the parts canonically, sort, keep one of each replication
      obtain ⟨readWell, readMembers, readDecode⟩ := decode_recanon reorderedWell locVariables context reorderedMembers
        (normalBelow.mono reorderedLighter)
      set read := reordered.map (recanon locatedRepBlock) with readIs
      have sortedPerm : (sortComponents read).Perm read := List.perm_insertionSort _ _
      have sortedWell : WellLocated isLoc (.bvar outer) ⟨pruned.count, sortComponents read⟩ :=
        readWell.drop locVariables (dropped := []) sortedPerm.symm (by simp)
      have sortedMembers : Members locatedCalc locatedBlock free (List.replicate pruned.count nameType ++ bound)
          (sortComponents read) := fun element member => readMembers element (sortedPerm.subset member)
      obtain ⟨removed, dedupPerm, removedFacts⟩ := dedupReplicated_split (sortComponents read)
      have dedupWell : WellLocated isLoc (.bvar outer)
          ⟨pruned.count, dedupReplicated locatedRepBlock (sortComponents read)⟩ :=
        sortedWell.drop locVariables (dedupPerm.trans List.perm_append_comm)
          fun component member index isPlaced marker inRemoved isChild => by
            obtain ⟨⟨argument, rfl⟩, -⟩ := removedFacts marker inRemoved
            simp [childOf] at isChild
      -- the canonical block is that reading
      have normalIs : normal locatedRepBlock ⟨count, components⟩ =
          ⟨pruned.count, dedupReplicated locatedRepBlock (sortComponents read)⟩ := by
        rw [normal_eq_reading]
        change (⟨pruned.count, Mettapedia.GSLT.LanguageDef.RestrictionBlocks.least
          (readingsR locatedRepBlock pruned)⟩ : Prenex) = _
        rw [leastIs, readIs, reorderedIs, List.map_map]
        rfl
      refine ⟨by rw [normalIs]; exact dedupWell, fun fuel enough normalEnough => ?_⟩
      -- read back with fuel enough for every step, then settle
      set big := fuel + roundsLeast + 3 * (reordered.map innerWeight).sum + 2 * reordered.length + 6 with bigIs
      obtain ⟨step, stepIs⟩ : ∃ step, big = step + 1 := ⟨big - 1, by omega⟩
      have chain : ProcEquiv ambientCoreCalc ambientBlock free bound
          (Prenex.toPattern ambientBlock (decodeForm big (.bvar outer) (normal locatedRepBlock ⟨count, components⟩)))
          (Prenex.toPattern ambientBlock (decodeForm big (.bvar outer) ⟨count, components⟩)) := by
        rw [normalIs, stepIs]
        refine .trans _ _ _ (decode_dedup step (.bvar outer) sortedMembers) ?_
        refine .trans _ _ _ (decode_perm step (.bvar outer) sortedPerm sortedMembers) ?_
        refine .trans _ _ _ (readDecode (step + 1) (by omega)) ?_
        refine .trans _ _ _ (decode_reorder step (.bvar outer) isOrder prunedMembers) ?_
        refine .trans _ _ _ (decode_prune step (.bvar outer) absorbedMembers) ?_
        exact Relation.EqvGen.symm _ _ (roundsDecode (step + 1) (by omega))
      rw [decodeForm_settled (.bvar outer) _ normalEnough (show 3 * (normal locatedRepBlock ⟨count, components⟩).mass + 3 ≤
          big by omega), decodeForm_settled (.bvar outer) ⟨count, components⟩ enough
          (show 3 * (Prenex.mk count components).mass + 3 ≤ big by omega)]
      exact chain

end Mettapedia.Languages.ProcessCalculi.Ambient.Decoding
