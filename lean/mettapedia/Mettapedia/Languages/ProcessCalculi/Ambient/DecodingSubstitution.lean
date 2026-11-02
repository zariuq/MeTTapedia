import Mettapedia.Languages.ProcessCalculi.Ambient.DecodingEncode
import Mettapedia.Languages.ProcessCalculi.Ambient.EncodingSubstitution
import Mettapedia.GSLT.LanguageDef.RestrictionBlocks.DecomposeSubstitution

/-!
# Reading back commutes with receiving a message

An input's body is a well-located block under the input's binder, which is never a location. When the input receives
a message, the body's block, the message substituted for the binder, reads back as the body's reading with the
message substituted (`decode_instantiate`).

The general statement is about an assignment a well-located block can receive (`LocatedAssignment`): every image a
message, names sent to variables, locations to variables, distinct locations kept distinct. Messages have no located
structure, so they are atoms of the located blocks (`messages_atomic`) and the block of a substituted process is the
block substituted past its restrictions; a substituted component sits at the substituted place (`placeAt_substitute`),
names stay names and messages stay messages, so the components placed at a location stay the components placed there
and the reading is substituted component by component (`decode_substitute`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.Ambient.Decoding

open Mettapedia.Languages.ProcessCalculi.Ambient.Comm (ambientCoreCalc capType)

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Substitution (liftBVars instantiateBVar)
open Mettapedia.OSLF.MeTTaIL.ContextSubstitution (Assignment substitute lift lift_zero substituteList_eq_map
  substitute_liftBVars single substitute_single_eq_instantiateBVar)
open Mettapedia.GSLT.LanguageDef.WellSorted (HasType FreeTypeContext isObjectPattern)
open Mettapedia.GSLT.LanguageDef.RestrictionBlocks (Prenex Members decompose size sizeList liftBVars_eq_rename
  AtomicImages decompose_substitute decompose_bvar_atom toPattern_substituteOuter substitute_body decompose_sound)
open Mettapedia.Languages.ProcessCalculi.Ambient.Full (ambientBlock)
open Mettapedia.Languages.ProcessCalculi.Ambient.Located (locatedCalc locatedBlock)
open Mettapedia.Languages.ProcessCalculi.Ambient.Encoding (nameType procType cap_apply_inv name_cases_located
  message_notLambda single_messages shiftName_eq_liftBVars substitute_single_shiftName)

/-! ## Messages are atoms with no place -/

/-- **A message is its own located block.** -/
theorem decompose_message {message : Pattern} (isMsg : isMessage message = true) :
    decompose locatedBlock message = Prenex.atom message := by
  refine Mettapedia.GSLT.LanguageDef.RestrictionBlocks.decompose_atom (fun same => ?_) (fun binder body same => ?_)
    (fun elements same => ?_) (fun label argument _ listed => by simp at listed)
  · subst same; simp [isMessage] at isMsg
  · subst same; simp [isMessage] at isMsg
  · subst same; simp [isMessage] at isMsg

/-- **An assignment of messages has atoms for images.** -/
theorem messages_atomic {assignment : Assignment} (messages : ∀ index, isMessage (assignment index) = true) :
    AtomicImages locatedBlock assignment := fun index =>
  ⟨decompose_message (messages index), message_notLambda (messages index)⟩

/-- Lifting past binders keeps an assignment of messages. -/
theorem messages_liftN {assignment : Assignment} (messages : ∀ index, isMessage (assignment index) = true)
    (arity : Nat) : ∀ index, isMessage (lift arity assignment index) = true := by
  intro index
  unfold Mettapedia.OSLF.MeTTaIL.ContextSubstitution.lift
  split_ifs
  · rfl
  · rw [liftBVars_eq_rename, isMessage_rename]
    exact messages _

/-- **A message sits at no place.** -/
theorem placeOf_message {message : Pattern} (isMsg : isMessage message = true) (fuel : Nat) :
    placeOf fuel message = none := by
  cases fuel with
  | zero => simp [placeOf]
  | succ fuel =>
      match message, isMsg with
      | .bvar _, _ => simp [placeOf]
      | .fvar _, _ => simp [placeOf]
      | .apply label [], _ => simp [placeOf]
      | .apply label [name], isMsg =>
          simp only [isMessage, Bool.and_eq_true, decide_eq_true_eq, List.mem_cons, List.not_mem_nil,
            or_false] at isMsg
          rcases isMsg.1 with rfl | rfl | rfl <;> simp [placeOf]
      | .apply label [first, second], isMsg =>
          simp only [isMessage, Bool.and_eq_true, beq_iff_eq] at isMsg
          obtain ⟨⟨rfl, -⟩, -⟩ := isMsg
          simp [placeOf, inputs, outputs]

/-! ## Names and messages received -/

/-- **A name stays a name** under an assignment sending names to variables. -/
theorem name_substitute {language : Mettapedia.OSLF.MeTTaIL.Syntax.LanguageDef} {free : FreeTypeContext}
    {bound : List TypeExpr} {assignment : Assignment}
    (names : ∀ index, bound[index]? = some nameType → isVariable (assignment index) = true) {name : Pattern}
    (typed : HasType language free bound name nameType) (isVar : isVariable name = true) :
    isVariable (substitute assignment name) = true := by
  cases name with
  | bvar index =>
      cases typed with
      | bvar found => exact names index found
  | fvar _ => rfl
  | _ => simp [isVariable] at isVar

/-- **A capability term stays a message** under an assignment of messages sending names to variables. -/
theorem cap_substitute {free : FreeTypeContext} {bound : List TypeExpr} {assignment : Assignment}
    (messages : ∀ index, isMessage (assignment index) = true)
    (names : ∀ index, bound[index]? = some nameType → isVariable (assignment index) = true) :
    ∀ {message : Pattern}, HasType ambientCoreCalc free bound message capType → isMessage message = true →
      isMessage (substitute assignment message) = true
  | .bvar index, _, _ => messages index
  | .fvar _, _, _ => rfl
  | .apply label [], _, isMsg => by simpa [substitute, isMessage] using isMsg
  | .apply label [name], typed, isMsg => by
      simp only [isMessage, Bool.and_eq_true, decide_eq_true_eq] at isMsg
      obtain ⟨listed, nameVar⟩ := isMsg
      rcases cap_apply_inv typed with ⟨-, name', same, nameTyped⟩ | ⟨-, same⟩ | ⟨-, _, _, same, -⟩
      · simp only [List.cons.injEq, and_true] at same
        subst same
        simp only [substitute, substituteList_eq_map, List.map_cons, List.map_nil, isMessage, Bool.and_eq_true,
          decide_eq_true_eq]
        exact ⟨listed, name_substitute names nameTyped nameVar⟩
      · simp at same
      · simp at same
  | .apply label [first, second], typed, isMsg => by
      simp only [isMessage, Bool.and_eq_true, beq_iff_eq] at isMsg
      obtain ⟨⟨rfl, firstMsg⟩, secondMsg⟩ := isMsg
      rcases cap_apply_inv typed with ⟨-, _, same, -⟩ | ⟨-, same⟩ |
        ⟨-, first', second', same, firstTyped, secondTyped⟩
      · simp at same
      · simp at same
      · simp only [List.cons.injEq, and_true] at same
        obtain ⟨rfl, rfl⟩ := same
        simp only [substitute, substituteList_eq_map, List.map_cons, List.map_nil, isMessage, Bool.and_eq_true,
          beq_iff_eq, true_and]
        exact ⟨cap_substitute messages names firstTyped firstMsg, cap_substitute messages names secondTyped secondMsg⟩
  | .apply _ (_ :: _ :: _ :: _), _, isMsg => by simp [isMessage] at isMsg
  | .lambda _ _, _, isMsg => by simp [isMessage] at isMsg
  | .multiLambda _ _ _, _, isMsg => by simp [isMessage] at isMsg
  | .subst _ _, _, isMsg => by simp [isMessage] at isMsg
  | .collection _ _ _, _, isMsg => by simp [isMessage] at isMsg

/-- **A message of a located calculus stays a message**, whatever its sort. -/
theorem message_substitute {free : FreeTypeContext} {bound : List TypeExpr} {assignment : Assignment}
    (messages : ∀ index, isMessage (assignment index) = true)
    (names : ∀ index, bound[index]? = some nameType → isVariable (assignment index) = true) {message : Pattern}
    {sort : String} (sorted : sort = "Name" ∨ sort = "Cap")
    (typed : HasType locatedCalc free bound message (.base sort)) (isMsg : isMessage message = true) :
    isMessage (substitute assignment message) = true := by
  rcases sorted with rfl | rfl
  · rcases name_cases_located typed rfl (message_object isMsg) with ⟨index, rfl, found⟩ | ⟨name, rfl, -⟩
    · exact message_of_variable (names index found)
    · rfl
  · exact cap_substitute messages names (message_typed typed isMsg) isMsg

/-! ## Places under substitution -/

/-- A variable lifted past a block's restrictions is lowered back out of it. -/
theorem lowerBy_lift_variable {count : Nat} {pattern : Pattern} (isVar : isVariable pattern = true) :
    lowerBy count (liftBVars 0 count pattern) = some pattern := by
  cases pattern with
  | bvar index => simp [liftBVars, lowerBy]
  | fvar name => simp [liftBVars, lowerBy]
  | _ => simp [isVariable] at isVar

/-- A substituted pattern that is no variable is no variable. -/
theorem substitute_notVariable {assignment : Assignment} {pattern : Pattern}
    (notVariable : isVariable pattern = false) : isVariable (substitute assignment pattern) = false := by
  cases pattern <;> simp_all [isVariable, substitute]

/-- What is not lowered out of a block is not lowered out of it substituted. -/
theorem lowerBy_substitute_none {count : Nat} {assignment : Assignment} {pattern : Pattern}
    (stays : lowerBy count pattern = none) : lowerBy count (substitute (lift count assignment) pattern) = none := by
  cases pattern with
  | bvar index =>
      simp only [lowerBy] at stays
      split_ifs at stays with above
      have below : index < count := by omega
      simp only [substitute]
      unfold Mettapedia.OSLF.MeTTaIL.ContextSubstitution.lift
      simp [below, lowerBy, show ¬ count ≤ index by omega]
  | fvar name => simp [lowerBy] at stays
  | _ => simp [substitute, lowerBy]

/-- **What is lowered out of a block is lowered out of it substituted**, when it receives a variable. -/
theorem lowerBy_substitute_some {count : Nat} {assignment : Assignment} {pattern lowered : Pattern}
    (out : lowerBy count pattern = some lowered)
    (receives : ∀ index, lowered = .bvar index → isVariable (assignment index) = true) :
    lowerBy count (substitute (lift count assignment) pattern) = some (substitute assignment lowered) := by
  cases pattern with
  | bvar index =>
      simp only [lowerBy] at out
      split_ifs at out with above
      cases out
      simp only [substitute]
      unfold Mettapedia.OSLF.MeTTaIL.ContextSubstitution.lift
      rw [if_neg (by omega)]
      exact lowerBy_lift_variable (receives _ rfl)
  | fvar name =>
      simp only [lowerBy, Option.some.injEq] at out
      subst out
      simp [substitute, lowerBy]
  | _ => simp [lowerBy] at out

/-- **The first found, mapped**: a search finding nothing where the original finds nothing, and the image of what
the original finds first. -/
theorem findSome?_map_of {first second : Pattern → Option Pattern} {image : Pattern → Pattern} :
    ∀ {list : List Pattern}, (∀ element ∈ list, first element = none → second element = none) →
      (∀ element ∈ list, ∀ found, first element = some found → list.findSome? first = some found →
        second element = some (image found)) →
      list.findSome? second = (list.findSome? first).map image
  | [], _, _ => rfl
  | element :: rest, nothing, something => by
      cases found : first element with
      | none =>
          rw [List.findSome?_cons_of_isNone (by rw [nothing element List.mem_cons_self found]; rfl),
            List.findSome?_cons_of_isNone (by rw [found]; rfl)]
          refine findSome?_map_of (fun other member => nothing other (List.mem_cons_of_mem _ member))
            fun other member result isFirst rest => something other (List.mem_cons_of_mem _ member) result isFirst ?_
          rwa [List.findSome?_cons_of_isNone (by rw [found]; rfl)]
      | some result =>
          have firstFound : (element :: rest).findSome? first = some result := by
            rw [List.findSome?_cons_of_isSome (by rw [found]; rfl), found]
          rw [firstFound, List.findSome?_cons_of_isSome (by
            rw [something element List.mem_cons_self result found firstFound]; rfl),
            something element List.mem_cons_self result found firstFound]
          rfl

/-- **Places are substituted with their components**, and outer places with what their blocks read from outside,
when the variables of the places found receive variables. -/
theorem places_substitute : ∀ (fuel : Nat),
    (∀ (assignment : Assignment) (component : Pattern), (∀ index, isMessage (assignment index) = true) →
      (∀ index, placeOf fuel component = some (.bvar index) → isVariable (assignment index) = true) →
      placeOf fuel (substitute assignment component) = (placeOf fuel component).map (substitute assignment)) ∧
    (∀ (assignment : Assignment) (form : Prenex), (∀ index, isMessage (assignment index) = true) →
      (∀ index, outerPlace fuel form = some (.bvar index) → isVariable (assignment index) = true) →
      outerPlace fuel (form.substituteOuter assignment) = (outerPlace fuel form).map (substitute assignment))
  | 0 => ⟨fun _ _ _ _ => by simp [placeOf], fun _ _ _ _ => by simp [outerPlace]⟩
  | fuel + 1 => by
      obtain ⟨placesBelow, outerBelow⟩ := places_substitute fuel
      refine ⟨fun assignment component messages found => ?_, fun assignment form messages found => ?_⟩
      · cases component with
        | bvar index =>
            rw [show substitute assignment (.bvar index) = assignment index from rfl,
              placeOf_message (messages index)]
            simp [placeOf]
        | apply label arguments =>
            match arguments, found with
            | [], _ => simp [substitute, placeOf]
            | [argument], found =>
                simp only [substitute, substituteList_eq_map, List.map_cons, List.map_nil, placeOf] at found ⊢
                split_ifs with isRep
                · rw [decompose_substitute (messages_atomic messages)]
                  exact outerBelow assignment _ messages fun index outer =>
                    found index (by rw [if_pos isRep]; exact outer)
                · rfl
            | [first, second, third], _ =>
                simp only [substitute, substituteList_eq_map, List.map_cons, List.map_nil, placeOf]
                split_ifs <;> rfl
            | [first, second], _ =>
                simp only [substitute, substituteList_eq_map, List.map_cons, List.map_nil, placeOf]
                split_ifs <;> rfl
            | _ :: _ :: _ :: _ :: _, _ => simp [substitute, placeOf]
        | _ => simp [substitute, placeOf]
      · obtain ⟨count, components⟩ := form
        simp only [Prenex.substituteOuter, outerPlace] at found ⊢
        rw [List.findSome?_map]
        refine findSome?_map_of (fun component member nothing => ?_) (fun component member lowered out first => ?_)
        · simp only [Function.comp]
          cases placed : placeOf fuel component with
          | none =>
              rw [placesBelow _ component (messages_liftN messages count)
                (fun index sits => by rw [placed] at sits; cases sits), placed]
              rfl
          | some place =>
              rw [placed, Option.bind_some] at nothing
              rw [placesBelow _ component (messages_liftN messages count) (fun index sits => by
                rw [placed, Option.some.injEq] at sits
                subst sits
                simp only [lowerBy] at nothing
                split_ifs at nothing with above
                unfold Mettapedia.OSLF.MeTTaIL.ContextSubstitution.lift
                rw [if_pos (by omega)]
                rfl), placed, Option.map_some, Option.bind_some]
              exact lowerBy_substitute_none nothing
        · simp only [Function.comp]
          cases placed : placeOf fuel component with
          | none => rw [placed] at out; cases out
          | some place =>
              rw [placed, Option.bind_some] at out
              have receives : ∀ index, lowered = .bvar index → isVariable (assignment index) = true :=
                fun index isLowered => found index (by rw [first, isLowered])
              rw [placesBelow _ component (messages_liftN messages count) (fun index sits => by
                rw [placed, Option.some.injEq] at sits
                subst sits
                simp only [lowerBy] at out
                split_ifs at out with above
                cases out
                unfold Mettapedia.OSLF.MeTTaIL.ContextSubstitution.lift
                rw [if_neg (by omega), isVariable_lift]
                exact receives _ rfl), placed, Option.map_some, Option.bind_some]
              exact lowerBy_substitute_some out receives

theorem sizeList_le_map {transform : Pattern → Pattern} :
    ∀ {list : List Pattern}, (∀ element ∈ list, size element ≤ size (transform element)) →
      sizeList list ≤ sizeList (list.map transform)
  | [], _ => le_refl _
  | element :: rest, each => by
      simp only [List.map_cons, sizeList]
      have here := each element List.mem_cons_self
      have later := sizeList_le_map (list := rest) fun other member => each other (List.mem_cons_of_mem _ member)
      omega

/-- **Substitution never shrinks a pattern.** -/
theorem size_le_substitute (pattern : Pattern) : ∀ (assignment : Assignment),
    size pattern ≤ size (substitute assignment pattern) := by
  induction pattern using Pattern.inductionOn with
  | hbvar index =>
      intro assignment
      show 1 ≤ size (assignment index)
      exact size_pos (assignment index)
  | hfvar => intro assignment; simp [substitute]
  | happly label arguments recurse =>
      intro assignment
      simp only [substitute, substituteList_eq_map, size]
      have := sizeList_le_map (transform := substitute assignment) fun argument member =>
        recurse argument member assignment
      omega
  | hlambda binder body recurse =>
      intro assignment
      simp only [substitute, size]
      have := recurse (lift 1 assignment)
      omega
  | hmultiLambda arity binders body recurse =>
      intro assignment
      simp only [substitute, size]
      have := recurse (lift arity assignment)
      omega
  | hsubst body replacement bodyRecurse replacementRecurse =>
      intro assignment
      simp only [substitute, size]
      have := bodyRecurse (lift 1 assignment)
      have := replacementRecurse assignment
      omega
  | hcollection kind elements rest recurse =>
      intro assignment
      simp only [substitute, substituteList_eq_map, size]
      have := sizeList_le_map (transform := substitute assignment) fun element member =>
        recurse element member assignment
      omega

/-- **A substituted component sits at the substituted place**, when its place's variable receives a variable. -/
theorem placeAt_substitute {assignment : Assignment} {component : Pattern}
    (messages : ∀ index, isMessage (assignment index) = true)
    (found : ∀ index, placeAt component = some (.bvar index) → isVariable (assignment index) = true) :
    placeAt (substitute assignment component) = (placeAt component).map (substitute assignment) := by
  have enough : 2 * size component + 1 ≤ 2 * size (substitute assignment component) + 1 := by
    have := size_le_substitute component assignment
    omega
  calc placeAt (substitute assignment component)
      = placeOf (2 * size (substitute assignment component) + 1) (substitute assignment component) := rfl
    _ = (placeOf (2 * size (substitute assignment component) + 1) component).map (substitute assignment) :=
        (places_substitute _).1 assignment component messages fun index sits =>
          found index (by rwa [placeOf_eq_placeAt enough] at sits)
    _ = (placeAt component).map (substitute assignment) := by rw [placeOf_eq_placeAt enough]


/-! ## Assignments a well-located block receives -/

/-- **An assignment a well-located block can receive**: a message for every variable, a variable for every name, a
variable for every location, and distinct locations kept distinct. -/
structure LocatedAssignment (isLoc : Pattern → Prop) (bound : List TypeExpr) (assignment : Assignment) : Prop where
  messages : ∀ index, isMessage (assignment index) = true
  names : ∀ index, bound[index]? = some nameType → isVariable (assignment index) = true
  places : ∀ location, isLoc location → isVariable (substitute assignment location) = true
  apart : ∀ first second, isLoc first → isLoc second →
    substitute assignment first = substitute assignment second → first = second

/-- A lifted variable is no variable bound below the lift. -/
theorem lift_ne_below {count index : Nat} {pattern : Pattern} (below : index < count) :
    liftBVars 0 count pattern ≠ .bvar index := by
  obtain ⟨previous, rfl⟩ : ∃ previous, count = previous + 1 := ⟨count - 1, by omega⟩
  exact liftBVars_ne_bvar previous pattern (by omega)

/-- **Locations outside a block, seen from inside**, are its outer locations lifted past its restrictions. -/
theorem insideLoc_outer {isLoc : Pattern → Prop} {count : Nat} {components : List Pattern} {location : Pattern}
    (inside : insideLoc isLoc count components location) :
    (∃ index < count, location = .bvar index) ∨ ∃ outer, isLoc outer ∧ location = liftBVars 0 count outer := by
  cases location with
  | bvar index =>
      simp only [insideLoc] at inside
      split_ifs at inside with below
      · exact .inl ⟨index, below, rfl⟩
      · exact .inr ⟨.bvar (index - count), inside, by simp [liftBVars]; omega⟩
  | fvar name => exact .inr ⟨.fvar name, inside, rfl⟩
  | _ => simp [insideLoc] at inside

/-- **Locations under a name binder, seen from outside it**, are the outer locations lifted past it. -/
theorem underName_outer {isLoc : Pattern → Prop} {location : Pattern} (under : underName isLoc location) :
    ∃ outer, isLoc outer ∧ location = liftBVars 0 1 outer := by
  cases location with
  | bvar index =>
      cases index with
      | zero => simp [underName] at under
      | succ index => exact ⟨.bvar index, under, by simp [liftBVars]⟩
  | fvar name => exact ⟨.fvar name, under, rfl⟩
  | _ => simp [underName] at under

theorem substitute_lift_outer (assignment : Assignment) (count : Nat) (outer : Pattern) :
    substitute (lift count assignment) (liftBVars 0 count outer) = liftBVars 0 count (substitute assignment outer) := by
  have shifted := substitute_liftBVars assignment outer 0 count
  rwa [Nat.zero_add, lift_zero] at shifted

theorem substitute_lift_below {assignment : Assignment} {count index : Nat} (below : index < count) :
    substitute (lift count assignment) (.bvar index) = .bvar index := by
  show lift count assignment index = _
  unfold Mettapedia.OSLF.MeTTaIL.ContextSubstitution.lift
  rw [if_pos below]

namespace LocatedAssignment

variable {isLoc : Pattern → Prop} {bound : List TypeExpr} {assignment : Assignment}

/-- **Inside a block**, the assignment lifted past its restrictions is one the block's components can receive. -/
theorem inBlock (assigned : LocatedAssignment isLoc bound assignment) (count : Nat) (components : List Pattern) :
    LocatedAssignment (insideLoc isLoc count components) (List.replicate count nameType ++ bound)
      (lift count assignment) where
  messages := messages_liftN assigned.messages count
  names := by
    intro index found
    unfold Mettapedia.OSLF.MeTTaIL.ContextSubstitution.lift
    split_ifs with below
    · rfl
    · rw [isVariable_lift]
      apply assigned.names
      rwa [List.getElem?_append_right (by simp; omega), List.length_replicate] at found
  places := by
    intro location inside
    rcases insideLoc_outer inside with ⟨index, below, rfl⟩ | ⟨outer, outerLoc, rfl⟩
    · rw [substitute_lift_below below]
      rfl
    · rw [substitute_lift_outer, isVariable_lift]
      exact assigned.places outer outerLoc
  apart := by
    intro first second firstInside secondInside same
    rcases insideLoc_outer firstInside with ⟨index, below, rfl⟩ | ⟨outer, outerLoc, rfl⟩ <;>
      rcases insideLoc_outer secondInside with ⟨index', below', rfl⟩ | ⟨outer', outerLoc', rfl⟩
    · rwa [substitute_lift_below below, substitute_lift_below below'] at same
    · rw [substitute_lift_below below, substitute_lift_outer] at same
      exact absurd same.symm (lift_ne_below below)
    · rw [substitute_lift_below below', substitute_lift_outer] at same
      exact absurd same (lift_ne_below below')
    · rw [substitute_lift_outer, substitute_lift_outer] at same
      rw [assigned.apart outer outer' outerLoc outerLoc' (liftBVars_injective count same)]

/-- **Under a name binder**, the assignment lifted past it is one the binder's body can receive. -/
theorem underBinder (assigned : LocatedAssignment isLoc bound assignment) (sort : TypeExpr) :
    LocatedAssignment (underName isLoc) (sort :: bound) (lift 1 assignment) where
  messages := messages_liftN assigned.messages 1
  names := by
    intro index found
    cases index with
    | zero => rfl
    | succ index =>
        unfold Mettapedia.OSLF.MeTTaIL.ContextSubstitution.lift
        rw [if_neg (by omega), isVariable_lift, Nat.add_sub_cancel]
        exact assigned.names index (by simpa using found)
  places := by
    intro location under
    obtain ⟨outer, outerLoc, rfl⟩ := underName_outer under
    rw [substitute_lift_outer, isVariable_lift]
    exact assigned.places outer outerLoc
  apart := by
    intro first second firstUnder secondUnder same
    obtain ⟨outer, outerLoc, rfl⟩ := underName_outer firstUnder
    obtain ⟨outer', outerLoc', rfl⟩ := underName_outer secondUnder
    rw [substitute_lift_outer, substitute_lift_outer] at same
    rw [assigned.apart outer outer' outerLoc outerLoc' (liftBVars_injective 1 same)]

end LocatedAssignment

/-! ## Reading back a block that received an assignment -/

/-- The place of a well-located block, seen from inside, is a location there. -/
theorem insideLoc_lifted {isLoc : Pattern → Prop} (locVariables : LocVariables isLoc) {place : Pattern}
    (placeLoc : isLoc place) (count : Nat) (components : List Pattern) :
    insideLoc isLoc count components (liftBVars 0 count place) := by
  have isVar := locVariables place placeLoc
  cases place with
  | bvar index =>
      simp only [liftBVars, Nat.zero_le, if_true, insideLoc]
      rw [if_neg (by omega), Nat.add_sub_cancel]
      exact placeLoc
  | fvar name => exact placeLoc
  | _ => simp [isVariable] at isVar

/-- A capability's continuation is a well-located block at the capability's place. -/
theorem WellLocated.capability_well {isLoc : Pattern → Prop} {place : Pattern} {count : Nat}
    {components : List Pattern} (well : WellLocated isLoc place ⟨count, components⟩) {label : String}
    {at' name continuation : Pattern} (member : .apply label [at', name, continuation] ∈ components)
    (listed : label ∈ capabilities) :
    WellLocated (insideLoc isLoc count components) at' (decompose locatedBlock continuation) := by
  cases well with
  | intro _ _ _ _ _ caps _ _ _ _ _ _ => exact caps _ member label at' name continuation rfl listed

/-- A replication's argument is a well-located block at the replication's place. -/
theorem WellLocated.rep_well {isLoc : Pattern → Prop} {place : Pattern} {count : Nat}
    {components : List Pattern} (well : WellLocated isLoc place ⟨count, components⟩) {argument at' : Pattern}
    (member : .apply "LRep" [argument] ∈ components) (sits : placeAt (.apply "LRep" [argument]) = some at') :
    WellLocated (insideLoc isLoc count components) at' (decompose locatedBlock argument) := by
  cases well with
  | intro _ _ _ _ _ _ reps _ _ _ _ _ => exact reps _ member argument at' rfl sits

theorem wrapContent_substitute (assignment : Assignment) (label : String) (name content : Pattern) :
    substitute assignment (wrapContent label name content) =
      wrapContent label (substitute assignment name) (substitute assignment content) := by
  unfold wrapContent
  split_ifs <;> simp [substitute, substituteList_eq_map]

variable {free : FreeTypeContext}

/-- **Reading back commutes with an assignment a well-located block can receive**: of a block's outer variables, of
the components placed at a location of a block, of one component placed at a location. -/
theorem decode_substitute : ∀ (fuel : Nat),
    (∀ {isLoc : Pattern → Prop} {bound : List TypeExpr} {assignment : Assignment} {place : Pattern} {form : Prenex},
      LocVariables isLoc → WellLocated isLoc place form →
      Members locatedCalc locatedBlock free (List.replicate form.count nameType ++ bound) form.components →
      LocatedAssignment isLoc bound assignment →
      decodeForm fuel (substitute assignment place) (form.substituteOuter assignment) =
        (decodeForm fuel place form).substituteOuter assignment) ∧
    (∀ {isLoc : Pattern → Prop} {bound : List TypeExpr} {assignment : Assignment} {outer : Pattern} {count : Nat}
        {all : List Pattern}, LocVariables isLoc → WellLocated isLoc outer ⟨count, all⟩ →
      Members locatedCalc locatedBlock free (List.replicate count nameType ++ bound) all →
      LocatedAssignment isLoc bound assignment →
      ∀ (place : Pattern) (components : List Pattern), insideLoc isLoc count all place →
        (∀ component ∈ components, component ∈ all) →
        readPlaced fuel (substitute (lift count assignment) place)
            (components.map (substitute (lift count assignment))) =
          (readPlaced fuel place components).map (substitute (lift count assignment))) ∧
    (∀ {isLoc : Pattern → Prop} {bound : List TypeExpr} {assignment : Assignment} {outer : Pattern} {count : Nat}
        {all : List Pattern}, LocVariables isLoc → WellLocated isLoc outer ⟨count, all⟩ →
      Members locatedCalc locatedBlock free (List.replicate count nameType ++ bound) all →
      LocatedAssignment isLoc bound assignment →
      ∀ (place component : Pattern) (components : List Pattern), component ∈ all →
        placeAt component = some place → (∀ other ∈ components, other ∈ all) →
        readComponent fuel (substitute (lift count assignment) place) (substitute (lift count assignment) component)
            (components.map (substitute (lift count assignment))) =
          substitute (lift count assignment) (readComponent fuel place component components))
  | 0 => by
      refine ⟨?_, ?_, ?_⟩
      · intro isLoc bound assignment place form _ _ _ _
        simp [decodeForm, Prenex.substituteOuter, Prenex.nil]
      · intro isLoc bound assignment outer count all _ _ _ _ place components _ _
        simp [readPlaced]
      · intro isLoc bound assignment outer count all _ _ _ _ place component components _ _ _
        simp [readComponent, inaction, substitute]
  | fuel + 1 => by
      have signature : Mettapedia.GSLT.LanguageDef.RestrictionBlocks.BlockSignature locatedCalc locatedBlock :=
        Mettapedia.Languages.ProcessCalculi.Ambient.Located.locatedLanguage.toBlockSignature
      obtain ⟨formsBelow, placedBelow, componentBelow⟩ := decode_substitute fuel
      refine ⟨?_, ?_, ?_⟩
      · intro isLoc bound assignment place form locVariables well typed assigned
        obtain ⟨count, all⟩ := form
        simp only [decodeForm, Prenex.substituteOuter]
        congr 1
        rw [← substitute_lift_outer]
        exact placedBelow locVariables well typed assigned _ all
          (insideLoc_lifted locVariables well.placeIsLoc count all) fun _ member => member
      · intro isLoc bound assignment outer count all locVariables well typed assigned place components inside within
        have assignedInside := assigned.inBlock count all
        have located : ∀ component ∈ all, ∀ at', placeAt component = some at' → insideLoc isLoc count all at' := by
          intro component member at' sits
          rcases well.placed component member at' sits with same | ⟨index, below, rfl, marked⟩
          · rw [same]
            exact insideLoc_lifted locVariables well.placeIsLoc count all
          · show insideLoc isLoc count all (.bvar index)
            simp only [insideLoc, if_pos below]
            exact marked
        have keep : ∀ component ∈ components, placedAt (substitute (lift count assignment) place)
            (substitute (lift count assignment) component) = placedAt place component := by
          intro component member
          have inAll := within component member
          simp only [placedAt]
          rw [placeAt_substitute assignedInside.messages
            (fun index sits => assignedInside.places _ (located component inAll _ sits))]
          cases sits : placeAt component with
          | none => simp
          | some at' =>
              simp only [Option.map_some]
              exact decide_eq_decide.mpr ⟨fun same => assignedInside.apart _ _ (located component inAll at' sits)
                inside same, fun same => by rw [same]⟩
        have filtered : ∀ (choose : Bool → Bool),
            (components.map (substitute (lift count assignment))).filter
                (fun component => choose (placedAt (substitute (lift count assignment) place) component)) =
              (components.filter fun component => choose (placedAt place component)).map
                (substitute (lift count assignment)) := by
          intro choose
          rw [List.filter_map]
          congr 1
          exact List.filter_congr fun component member => by simp [Function.comp, keep component member]
        have here := filtered id
        have elsewhere := filtered (fun placed => !placed)
        simp only [id] at here elsewhere
        simp only [readPlaced]
        rw [here, elsewhere, List.map_map, List.map_map]
        refine List.map_congr_left fun component member => ?_
        obtain ⟨inComponents, isPlaced⟩ := List.mem_filter.mp member
        simp only [Function.comp]
        exact componentBelow locVariables well typed assigned place component _ (within _ inComponents)
          (by simpa [placedAt] using isPlaced) fun other otherIn => within other (List.mem_filter.mp otherIn).1
      · intro isLoc bound assignment outer count all locVariables well typed assigned place component components
          member placed within
        have assignedInside := assigned.inBlock count all
        have componentTyped := typed component member
        cases well.kinds component member with
        | @marker label parent name index isMarker below =>
            rw [placeAt_ofMarker isMarker] at placed
            cases placed
            have nameVar : isVariable name = true := (well.names _ member name (by simp [nameOf, isMarker])).1
            have nameTyped : HasType locatedCalc free (List.replicate count nameType ++ bound) name nameType := by
              rcases triple_inv componentTyped with ⟨-, -, third⟩ | ⟨listed, -, -⟩ | ⟨rfl, -, -⟩
              · exact third
              · exact absurd listed (not_capability_of_marker isMarker)
              · simp [markers] at isMarker
            have nameVar' := name_substitute assignedInside.names nameTyped nameVar
            have marked : insideLoc isLoc count all (.bvar index) := by
              simp only [insideLoc, if_pos below]
              exact ⟨_, member, childOf_ofMarker isMarker _ _ _⟩
            have inner := placedBelow locVariables well typed assigned (.bvar index) components marked within
            rw [substitute_lift_below below] at inner
            simp only [substitute, substituteList_eq_map, List.map_cons, List.map_nil]
            rw [show lift count assignment index = .bvar index from substitute_lift_below below]
            simp only [readComponent, if_pos isMarker]
            rw [if_pos nameVar', if_pos nameVar, inner, wrapContent_substitute, substitute_body]
        | @capability label at' name continuation listed =>
            rw [placeAt_capability listed] at placed
            cases placed
            have nameVar : isVariable name = true :=
              (well.names _ member name (by simp [nameOf, not_marker_of_capability listed, listed])).1
            obtain ⟨nameTyped, continuationTyped⟩ : HasType locatedCalc free (List.replicate count nameType ++ bound)
                name nameType ∧ HasType locatedCalc free (List.replicate count nameType ++ bound) continuation
                  procType := by
              rcases triple_inv componentTyped with ⟨isMarker, -, -⟩ | ⟨-, second, third⟩ | ⟨rfl, -, -⟩
              · exact absurd listed (not_capability_of_marker isMarker)
              · exact ⟨second, third⟩
              · simp [capabilities] at listed
            have nameVar' := name_substitute assignedInside.names nameTyped nameVar
            have inner := formsBelow (insideLoc_locVariables isLoc count all) (well.capability_well member listed)
              (decompose_sound (language := locatedCalc) (block := locatedBlock) continuationTyped).1 assignedInside
            simp only [substitute, substituteList_eq_map, List.map_cons, List.map_nil]
            simp only [readComponent, if_neg (not_marker_of_capability listed), if_pos listed]
            rw [if_pos nameVar', if_pos nameVar, decompose_substitute (messages_atomic assignedInside.messages),
              inner, toPattern_substituteOuter]
            simp [substitute, substituteList_eq_map]
        | @replication argument =>
            have inner := formsBelow (insideLoc_locVariables isLoc count all) (well.rep_well member placed)
              (decompose_sound (language := locatedCalc) (block := locatedBlock) (rep_inv componentTyped)).1
              assignedInside
            simp only [substitute, substituteList_eq_map, List.map_cons, List.map_nil]
            simp only [readComponent, if_true]
            rw [decompose_substitute (messages_atomic assignedInside.messages), inner, toPattern_substituteOuter]
            simp [substitute, substituteList_eq_map]
        | @cap at' message continuation =>
            rw [placeAt_cap] at placed
            cases placed
            have messageIs := (well.messages _ member message (by simp [messageOf])).1
            obtain ⟨messageTyped, continuationTyped⟩ : HasType locatedCalc free
                (List.replicate count nameType ++ bound) message capType ∧
                HasType locatedCalc free (List.replicate count nameType ++ bound) continuation procType := by
              rcases triple_inv componentTyped with ⟨isMarker, -, -⟩ | ⟨listed, -, -⟩ | ⟨-, second, third⟩
              · simp [markers] at isMarker
              · simp [capabilities] at listed
              · exact ⟨second, third⟩
            have messageIs' := message_substitute assignedInside.messages assignedInside.names (.inr rfl) messageTyped
              messageIs
            have inner := formsBelow (insideLoc_locVariables isLoc count all) (well.capConts _ member _ message
              continuation rfl) (decompose_sound (language := locatedCalc) (block := locatedBlock)
                continuationTyped).1 assignedInside
            simp only [substitute, substituteList_eq_map, List.map_cons, List.map_nil]
            simp only [readComponent, show "LCap" ∉ markers by simp [markers],
              show "LCap" ∉ capabilities by simp [capabilities], if_false, if_true]
            rw [if_pos messageIs', if_pos messageIs, decompose_substitute (messages_atomic assignedInside.messages),
              inner, toPattern_substituteOuter]
            simp [substitute, substituteList_eq_map]
        | @input label at' binder body listed =>
            rw [placeAt_input listed] at placed
            cases placed
            obtain ⟨sort, bodyTyped⟩ : ∃ sort : String,
                HasType locatedCalc free (.base sort :: (List.replicate count nameType ++ bound)) body procType := by
              rcases (pair_inv componentTyped).2 with ⟨sort, body', -, same, typed'⟩ | ⟨sort, listed', -⟩
              · simp only [Pattern.lambda.injEq] at same
                obtain ⟨-, rfl⟩ := same
                exact ⟨sort, typed'⟩
              · exact absurd listed (not_input_of_output (by
                  simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at listed'
                  rcases listed' with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> simp [outputs]))
            have assignedBody := assignedInside.underBinder (.base sort)
            have inner := formsBelow (underName_locVariables _)
              (well.bodies _ member label _ binder body rfl listed)
              (decompose_sound (language := locatedCalc) (block := locatedBlock) bodyTyped).1 assignedBody
            simp only [substitute, substituteList_eq_map, List.map_cons, List.map_nil]
            rw [readComponent_input listed, readComponent_input listed]
            simp only [substitute, substituteList_eq_map, List.map_cons, List.map_nil, decodeAt]
            rw [← substitute_lift_outer, decompose_substitute (messages_atomic assignedBody.messages), inner,
              toPattern_substituteOuter]
        | @output label at' message listed =>
            rw [placeAt_output listed] at placed
            cases placed
            have messageIs := (well.messages _ member message (by
              simp [messageOf, listed])).1
            obtain ⟨sort, sorted, messageTyped⟩ : ∃ sort : String, (sort = "Name" ∨ sort = "Cap") ∧
                HasType locatedCalc free (List.replicate count nameType ++ bound) message (.base sort) := by
              rcases (pair_inv componentTyped).2 with ⟨sort, body', listed', -, -⟩ | ⟨sort, listed', typed'⟩
              · exact absurd (by
                  simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at listed'
                  rcases listed' with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> simp [inputs]) (not_input_of_output listed)
              · simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at listed'
                rcases listed' with ⟨-, rfl⟩ | ⟨-, rfl⟩
                · exact ⟨_, .inl rfl, typed'⟩
                · exact ⟨_, .inr rfl, typed'⟩
            have messageIs' := message_substitute assignedInside.messages assignedInside.names sorted messageTyped
              messageIs
            simp only [substitute, substituteList_eq_map, List.map_cons, List.map_nil]
            rw [readComponent_output listed, readComponent_output listed, if_pos messageIs', if_pos messageIs]
            simp [substitute, substituteList_eq_map]

/-- **Reading a process back commutes with an assignment its well-located block can receive.** -/
theorem decodeAt_substitute {isLoc : Pattern → Prop} {bound : List TypeExpr} {assignment : Assignment}
    {place process : Pattern} (locVariables : LocVariables isLoc)
    (well : WellLocated isLoc place (decompose locatedBlock process))
    (typed : HasType locatedCalc free bound process procType)
    (assigned : LocatedAssignment isLoc bound assignment) (fuel : Nat) :
    decodeAt fuel (substitute assignment place) (substitute assignment process) =
      substitute assignment (decodeAt fuel place process) := by
  have signature : Mettapedia.GSLT.LanguageDef.RestrictionBlocks.BlockSignature locatedCalc locatedBlock :=
    Mettapedia.Languages.ProcessCalculi.Ambient.Located.locatedLanguage.toBlockSignature
  unfold decodeAt
  rw [decompose_substitute (messages_atomic assigned.messages),
    (decode_substitute fuel).1 locVariables well
      (decompose_sound (language := locatedCalc) (block := locatedBlock) typed).1 assigned,
    toPattern_substituteOuter]

/-- **A message received by the binder of an input's body**, never a location, and a variable where the binder is a
name, is an assignment the body can receive. -/
theorem single_located {isLoc : Pattern → Prop} {bound : List TypeExpr} {sort : TypeExpr} {message : Pattern}
    (isMsg : isMessage message = true) (nameVar : sort = nameType → isVariable message = true) :
    LocatedAssignment (underName isLoc) (sort :: bound) (single message) where
  messages := single_messages isMsg
  names := by
    intro index found
    cases index with
    | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at found
        exact nameVar found
    | succ index => rfl
  places := by
    intro location under
    have isVar := underName_locVariables isLoc location under
    obtain ⟨outer, -, rfl⟩ := underName_outer under
    rw [← shiftName_eq_liftBVars, substitute_single_shiftName]
    rwa [isVariable_lift] at isVar
  apart := by
    intro first second firstUnder secondUnder same
    obtain ⟨outer, -, rfl⟩ := underName_outer firstUnder
    obtain ⟨outer', -, rfl⟩ := underName_outer secondUnder
    rw [← shiftName_eq_liftBVars, ← shiftName_eq_liftBVars, substitute_single_shiftName,
      substitute_single_shiftName] at same
    rw [same]

/-- **An input's body, receiving a message, reads back as its reading receiving the message**: the binder is never a
location, and receives a variable where it is a name. -/
theorem decode_instantiate {isLoc : Pattern → Prop} {bound : List TypeExpr} {sort : TypeExpr}
    {place body message : Pattern}
    (well : WellLocated (underName isLoc) (liftBVars 0 1 place) (decompose locatedBlock body))
    (typed : HasType locatedCalc free (sort :: bound) body procType)
    (isMsg : isMessage message = true) (nameVar : sort = nameType → isVariable message = true) (fuel : Nat) :
    decodeAt fuel place (instantiateBVar message body) =
      instantiateBVar message (decodeAt fuel (liftBVars 0 1 place) body) := by
  have placeIs : substitute (single message) (liftBVars 0 1 place) = place := by
    rw [← shiftName_eq_liftBVars, substitute_single_shiftName]
  rw [← substitute_single_eq_instantiateBVar message body,
    ← substitute_single_eq_instantiateBVar message (decodeAt fuel (liftBVars 0 1 place) body),
    ← decodeAt_substitute (underName_locVariables isLoc) well typed (single_located isMsg nameVar) fuel, placeIs]

end Mettapedia.Languages.ProcessCalculi.Ambient.Decoding
