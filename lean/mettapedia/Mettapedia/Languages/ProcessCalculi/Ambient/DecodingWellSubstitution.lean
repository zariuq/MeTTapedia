import Mettapedia.Languages.ProcessCalculi.Ambient.DecodingSubstitution

/-!
# A well-located block receiving an assignment

A well-located block whose outside receives an assignment stays well-located (`WellLocated.substituteOuter`), when the
assignment sends names to variables and messages to messages, sends a variable to a location exactly when the
variable is one, and sends a variable that is no location to terms whose variables are no locations. Inside the block
its own restrictions are untouched, so the locations its markers place ambients at stay its locations
(`marked_substitute`), and locations, names and messages read through the assignment as they read before
(`insideLoc_substitute`, `insideLoc_apart`).

In particular an input's body, receiving a message whose variables are no locations, is a well-located block at the
input's place (`WellLocated.instantiate`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.Ambient.Decoding

open Mettapedia.Languages.ProcessCalculi.Ambient.Comm (capType)

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Substitution (liftBVars instantiateBVar)
open Mettapedia.OSLF.MeTTaIL.ContextSubstitution (Assignment substitute lift lift_zero substituteList_eq_map
  substitute_liftBVars single substitute_single_eq_instantiateBVar)
open Mettapedia.GSLT.LanguageDef.WellSorted (HasType FreeTypeContext isObjectPattern)
open Mettapedia.GSLT.LanguageDef.RestrictionBlocks (Prenex Members decompose liftBVars_eq_rename
  decompose_substitute decompose_sound)
open Mettapedia.Languages.ProcessCalculi.Ambient.Located (locatedCalc locatedBlock)
open Mettapedia.Languages.ProcessCalculi.Ambient.Encoding (nameType procType single_messages shiftName_eq_liftBVars
  substitute_single_shiftName)

/-! ## Names, messages and children under substitution -/

theorem lift_apply_below {assignment : Assignment} {count index : Nat} (below : index < count) :
    lift count assignment index = .bvar index := substitute_lift_below below

/-- Names receive variables past a block's restrictions. -/
theorem names_liftN {bound : List TypeExpr} {assignment : Assignment}
    (names : ∀ index, bound[index]? = some nameType → isVariable (assignment index) = true) (count : Nat) :
    ∀ index, (List.replicate count nameType ++ bound)[index]? = some nameType →
      isVariable (lift count assignment index) = true := by
  intro index found
  unfold Mettapedia.OSLF.MeTTaIL.ContextSubstitution.lift
  split_ifs with below
  · rfl
  · rw [isVariable_lift]
    apply names
    rwa [List.getElem?_append_right (by simp; omega), List.length_replicate] at found

/-- Names receive variables past a binder. -/
theorem names_cons {bound : List TypeExpr} {assignment : Assignment}
    (names : ∀ index, bound[index]? = some nameType → isVariable (assignment index) = true) (sort : TypeExpr) :
    ∀ index, (sort :: bound)[index]? = some nameType → isVariable (lift 1 assignment index) = true := by
  intro index found
  cases index with
  | zero => rfl
  | succ index =>
      unfold Mettapedia.OSLF.MeTTaIL.ContextSubstitution.lift
      rw [if_neg (by omega), isVariable_lift, Nat.add_sub_cancel]
      exact names index (by simpa using found)

/-- A message places no ambient. -/
theorem childOf_message {message : Pattern} (isMsg : isMessage message = true) : childOf message = none := by
  match message, isMsg with
  | .bvar _, _ => rfl
  | .fvar _, _ => rfl
  | .apply _ [], _ => rfl
  | .apply _ [_], _ => rfl
  | .apply _ [_, _], _ => rfl

/-- **A substituted marker places its ambient at the substituted location.** -/
theorem childOf_substitute {assignment : Assignment} (messages : ∀ index, isMessage (assignment index) = true)
    (component : Pattern) : childOf (substitute assignment component) = (childOf component).map (substitute assignment) := by
  cases component with
  | bvar index => exact childOf_message (messages index)
  | apply label arguments =>
      match arguments with
      | [_, _, _] =>
          simp only [substitute, substituteList_eq_map, List.map_cons, List.map_nil, childOf]
          split_ifs <;> rfl
      | [] => simp [substitute, childOf]
      | [_] => simp [substitute, substituteList_eq_map, childOf]
      | [_, _] => simp [substitute, substituteList_eq_map, childOf]
      | _ :: _ :: _ :: _ :: _ => simp [substitute, substituteList_eq_map, childOf]
  | _ => simp [substitute, childOf]

/-- A message holds no name. -/
theorem nameOf_message {message : Pattern} (isMsg : isMessage message = true) : nameOf message = none := by
  match message, isMsg with
  | .bvar _, _ => rfl
  | .fvar _, _ => rfl
  | .apply _ [], _ => rfl
  | .apply _ [_], _ => rfl
  | .apply _ [_, _], _ => rfl

theorem nameOf_substitute {assignment : Assignment} (messages : ∀ index, isMessage (assignment index) = true)
    (component : Pattern) : nameOf (substitute assignment component) = (nameOf component).map (substitute assignment) := by
  cases component with
  | bvar index => exact nameOf_message (messages index)
  | apply label arguments =>
      match arguments with
      | [_, _, _] =>
          simp only [substitute, substituteList_eq_map, List.map_cons, List.map_nil, nameOf]
          split_ifs <;> rfl
      | [] => simp [substitute, nameOf]
      | [_] => simp [substitute, substituteList_eq_map, nameOf]
      | [_, _] => simp [substitute, substituteList_eq_map, nameOf]
      | _ :: _ :: _ :: _ :: _ => simp [substitute, substituteList_eq_map, nameOf]
  | _ => simp [substitute, nameOf]

/-- A message holds no message of a component. -/
theorem messageOf_message {message : Pattern} (isMsg : isMessage message = true) : messageOf message = none := by
  match message, isMsg with
  | .bvar _, _ => rfl
  | .fvar _, _ => rfl
  | .apply _ [], _ => rfl
  | .apply _ [_], _ => rfl
  | .apply label [_, _], isMsg =>
      simp only [isMessage, Bool.and_eq_true, beq_iff_eq] at isMsg
      obtain ⟨⟨rfl, -⟩, -⟩ := isMsg
      simp [messageOf, outputs]

theorem messageOf_substitute {assignment : Assignment} (messages : ∀ index, isMessage (assignment index) = true)
    (component : Pattern) :
    messageOf (substitute assignment component) = (messageOf component).map (substitute assignment) := by
  cases component with
  | bvar index => exact messageOf_message (messages index)
  | apply label arguments =>
      match arguments with
      | [_, _, _] =>
          simp only [substitute, substituteList_eq_map, List.map_cons, List.map_nil, messageOf]
          split_ifs <;> rfl
      | [_, _] =>
          simp only [substitute, substituteList_eq_map, List.map_cons, List.map_nil, messageOf]
          split_ifs <;> rfl
      | [] => simp [substitute, messageOf]
      | [_] => simp [substitute, substituteList_eq_map, messageOf]
      | _ :: _ :: _ :: _ :: _ => simp [substitute, substituteList_eq_map, messageOf]
  | _ => simp [substitute, messageOf]

/-- **The variables of a substituted message are the variables of what its variables receive.** -/
theorem messageVariables_substitute {assignment : Assignment} : ∀ (message : Pattern) {name : Pattern},
    name ∈ messageVariables (substitute assignment message) →
      ∃ held ∈ messageVariables message, name ∈ messageVariables (substitute assignment held)
  | .bvar index, _, member => ⟨.bvar index, by simp [messageVariables], member⟩
  | .fvar other, _, member => ⟨.fvar other, by simp [messageVariables], member⟩
  | .apply _ [], _, member => by simp [substitute, messageVariables] at member
  | .apply _ [inner], _, member => by
      simp only [substitute, substituteList_eq_map, List.map_cons, List.map_nil, messageVariables] at member
      obtain ⟨held, inInner, inImage⟩ := messageVariables_substitute inner member
      exact ⟨held, by simpa [messageVariables] using inInner, inImage⟩
  | .apply _ [first, second], _, member => by
      simp only [substitute, substituteList_eq_map, List.map_cons, List.map_nil, messageVariables,
        List.mem_append] at member
      rcases member with inFirst | inSecond
      · obtain ⟨held, inOriginal, inImage⟩ := messageVariables_substitute first inFirst
        exact ⟨held, by simp [messageVariables, inOriginal], inImage⟩
      · obtain ⟨held, inOriginal, inImage⟩ := messageVariables_substitute second inSecond
        exact ⟨held, by simp [messageVariables, inOriginal], inImage⟩
  | .apply _ (_ :: _ :: _ :: _), _, member => by simp [substitute, substituteList_eq_map, messageVariables] at member
  | .lambda _ _, _, member => by simp [substitute, messageVariables] at member
  | .multiLambda _ _ _, _, member => by simp [substitute, messageVariables] at member
  | .subst _ _, _, member => by simp [substitute, messageVariables] at member
  | .collection _ _ _, _, member => by simp [substitute, substituteList_eq_map, messageVariables] at member

/-- The variables of a lifted message are its variables, lifted. -/
theorem messageVariables_lift (count : Nat) (message : Pattern) :
    messageVariables (liftBVars 0 count message) = (messageVariables message).map (liftBVars 0 count) := by
  rw [liftBVars_eq_rename, messageVariables_rename]
  simp only [List.map_inj_left]
  intro name _
  rw [liftBVars_eq_rename]

/-! ## Locations under substitution -/

/-- **A block's locations stay its locations**: its markers place ambients at its own restrictions, which the
assignment past them does not reach. -/
theorem marked_substitute {count : Nat} {assignment : Assignment}
    (messages : ∀ index, isMessage (assignment index) = true) {components : List Pattern}
    (kinds : ∀ component ∈ components, ComponentKind count component) {index : Nat} :
    Marked (components.map (substitute (lift count assignment))) index ↔ Marked components index := by
  constructor
  · rintro ⟨component, member, isChild⟩
    obtain ⟨original, inComponents, rfl⟩ := List.mem_map.mp member
    rw [childOf_substitute (messages_liftN messages count)]
      at isChild
    cases found : childOf original with
    | none => rw [found] at isChild; cases isChild
    | some child =>
        rw [found, Option.map_some, Option.some.injEq] at isChild
        obtain ⟨childIndex, childBelow, rfl⟩ := childOf_bvar_of_kind (kinds original inComponents) found
        rw [substitute_lift_below childBelow] at isChild
        exact ⟨original, inComponents, by rw [found, isChild]⟩
  · rintro ⟨component, member, isChild⟩
    refine ⟨substitute (lift count assignment) component, List.mem_map.mpr ⟨component, member, rfl⟩, ?_⟩
    obtain ⟨childIndex, childBelow, same⟩ := childOf_bvar_of_kind (kinds component member) isChild
    simp only [Pattern.bvar.injEq] at same
    subst same
    rw [childOf_substitute (messages_liftN messages count),
      isChild, Option.map_some, substitute_lift_below childBelow]

/-- A lifted pattern is a location inside a block exactly when it is one outside, for locations that are variables. -/
theorem insideLoc_lift_iff {isLoc : Pattern → Prop} (locVariables : LocVariables isLoc) (count : Nat)
    (components : List Pattern) (pattern : Pattern) :
    insideLoc isLoc count components (liftBVars 0 count pattern) ↔ isLoc pattern := by
  cases pattern with
  | bvar index =>
      simp only [liftBVars, Nat.zero_le, if_true, insideLoc]
      rw [if_neg (by omega), Nat.add_sub_cancel]
  | fvar name => rfl
  | _ =>
      constructor
      · intro inside
        simp [liftBVars, insideLoc] at inside
      · intro isLocation
        have := locVariables _ isLocation
        simp [isVariable] at this

/-- A lifted variable is a location inside a block exactly when it is one outside. -/
theorem insideLoc_lift_variable {isLoc : Pattern → Prop} (count : Nat) (components : List Pattern)
    {pattern : Pattern} (isVar : isVariable pattern = true) :
    insideLoc isLoc count components (liftBVars 0 count pattern) ↔ isLoc pattern := by
  cases pattern with
  | bvar index =>
      simp only [liftBVars, Nat.zero_le, if_true, insideLoc]
      rw [if_neg (by omega), Nat.add_sub_cancel]
  | fvar name => rfl
  | _ => simp [isVariable] at isVar

/-- A variable is one of a block's restrictions or a lifted variable from outside it. -/
theorem variable_inside_or_outer {pattern : Pattern} (isVar : isVariable pattern = true) (count : Nat) :
    (∃ index < count, pattern = .bvar index) ∨
      ∃ outer, isVariable outer = true ∧ pattern = liftBVars 0 count outer := by
  cases pattern with
  | bvar index =>
      by_cases below : index < count
      · exact .inl ⟨index, below, rfl⟩
      · exact .inr ⟨.bvar (index - count), rfl, by simp [liftBVars]; omega⟩
  | fvar name => exact .inr ⟨.fvar name, rfl, rfl⟩
  | _ => simp [isVariable] at isVar

/-- **Locations inside a block read through an assignment of its outside** as they read before. -/
theorem insideLoc_substitute {isLoc isLoc' : Pattern → Prop} {assignment : Assignment}
    (compat : ∀ pattern, isVariable pattern = true → (isLoc' (substitute assignment pattern) ↔ isLoc pattern))
    (locVariables' : LocVariables isLoc') {count : Nat} {components : List Pattern}
    (sameMarked : ∀ index, Marked (components.map (substitute (lift count assignment))) index ↔
      Marked components index) :
    ∀ pattern, isVariable pattern = true →
      (insideLoc isLoc' count (components.map (substitute (lift count assignment)))
          (substitute (lift count assignment) pattern) ↔ insideLoc isLoc count components pattern) := by
  intro pattern isVar
  rcases variable_inside_or_outer isVar count with ⟨index, below, rfl⟩ | ⟨outer, outerVar, rfl⟩
  · rw [substitute_lift_below below]
    simp only [insideLoc, if_pos below]
    exact sameMarked index
  · rw [substitute_lift_outer, insideLoc_lift_iff locVariables', insideLoc_lift_variable count components outerVar]
    exact compat outer outerVar

/-- **What no location inside a block receives holds no location**, read through an assignment of the outside. -/
theorem insideLoc_apart {isLoc isLoc' : Pattern → Prop} {assignment : Assignment}
    (apart : ∀ pattern, isVariable pattern = true → ¬ isLoc pattern →
      ∀ name ∈ messageVariables (substitute assignment pattern), ¬ isLoc' name)
    {count : Nat} {components : List Pattern}
    (sameMarked : ∀ index, Marked (components.map (substitute (lift count assignment))) index ↔
      Marked components index) :
    ∀ pattern, isVariable pattern = true → ¬ insideLoc isLoc count components pattern →
      ∀ name ∈ messageVariables (substitute (lift count assignment) pattern),
        ¬ insideLoc isLoc' count (components.map (substitute (lift count assignment))) name := by
  intro pattern isVar notInside name member inside
  rcases variable_inside_or_outer isVar count with ⟨index, below, rfl⟩ | ⟨outer, outerVar, rfl⟩
  · rw [substitute_lift_below below] at member
    simp only [messageVariables, List.mem_singleton] at member
    subst member
    simp only [insideLoc, if_pos below] at inside notInside
    exact notInside ((sameMarked index).mp inside)
  · rw [substitute_lift_outer, messageVariables_lift] at member
    obtain ⟨inner, innerIn, rfl⟩ := List.mem_map.mp member
    rw [insideLoc_lift_variable count _ (isVariable_of_messageVariables innerIn)] at inside
    rw [insideLoc_lift_variable count components outerVar] at notInside
    exact apart outer outerVar notInside inner innerIn inside

/-- A lifted pattern is a location under a name binder exactly when it is one outside. -/
theorem underName_lift_iff {isLoc : Pattern → Prop} (locVariables : LocVariables isLoc) (pattern : Pattern) :
    underName isLoc (liftBVars 0 1 pattern) ↔ isLoc pattern := by
  cases pattern with
  | bvar index => simp [liftBVars, underName]
  | fvar name => rfl
  | _ =>
      constructor
      · intro under
        simp [liftBVars, underName] at under
      · intro isLocation
        have := locVariables _ isLocation
        simp [isVariable] at this

/-- **Locations under a name binder read through an assignment lifted past it** as they read before. -/
theorem underName_substitute {isLoc isLoc' : Pattern → Prop} {assignment : Assignment}
    (compat : ∀ pattern, isVariable pattern = true → (isLoc' (substitute assignment pattern) ↔ isLoc pattern))
    (locVariables' : LocVariables isLoc') :
    ∀ pattern, isVariable pattern = true →
      (underName isLoc' (substitute (lift 1 assignment) pattern) ↔ underName isLoc pattern) := by
  intro pattern isVar
  cases pattern with
  | bvar index =>
      cases index with
      | zero => simp [substitute, Mettapedia.OSLF.MeTTaIL.ContextSubstitution.lift, underName]
      | succ index =>
          have outer := compat (.bvar index) rfl
          show underName isLoc' (lift 1 assignment (index + 1)) ↔ isLoc (.bvar index)
          unfold Mettapedia.OSLF.MeTTaIL.ContextSubstitution.lift
          rw [if_neg (by omega), Nat.add_sub_cancel, underName_lift_iff locVariables']
          exact outer
  | fvar name => exact compat (.fvar name) rfl
  | _ => simp [isVariable] at isVar

/-- **What no location under a name binder receives holds no location**, through an assignment lifted past it. -/
theorem underName_apart {isLoc isLoc' : Pattern → Prop} {assignment : Assignment}
    (apart : ∀ pattern, isVariable pattern = true → ¬ isLoc pattern →
      ∀ name ∈ messageVariables (substitute assignment pattern), ¬ isLoc' name)
    (locVariables' : LocVariables isLoc') :
    ∀ pattern, isVariable pattern = true → ¬ underName isLoc pattern →
      ∀ name ∈ messageVariables (substitute (lift 1 assignment) pattern), ¬ underName isLoc' name := by
  intro pattern isVar notUnder name member under
  cases pattern with
  | bvar index =>
      cases index with
      | zero =>
          simp [substitute, Mettapedia.OSLF.MeTTaIL.ContextSubstitution.lift, messageVariables] at member
          subst member
          simp [underName] at under
      | succ index =>
          have moved : substitute (lift 1 assignment) (.bvar (index + 1)) =
              liftBVars 0 1 (substitute assignment (.bvar index)) := by
            show lift 1 assignment (index + 1) = _
            unfold Mettapedia.OSLF.MeTTaIL.ContextSubstitution.lift
            rw [if_neg (by omega), Nat.add_sub_cancel]
            rfl
          rw [moved, messageVariables_lift] at member
          obtain ⟨inner, innerIn, rfl⟩ := List.mem_map.mp member
          have innerVar := isVariable_of_messageVariables innerIn
          rw [underName_lift_iff locVariables'] at under
          exact apart (.bvar index) rfl notUnder inner innerIn under
  | fvar fname =>
      have moved : substitute (lift 1 assignment) (.fvar fname) = liftBVars 0 1 (substitute assignment (.fvar fname)) := rfl
      rw [moved, messageVariables_lift] at member
      obtain ⟨inner, innerIn, rfl⟩ := List.mem_map.mp member
      rw [underName_lift_iff locVariables'] at under
      exact apart (.fvar fname) rfl notUnder inner innerIn under
  | _ => simp [isVariable] at isVar

/-! ## Typing of what a component holds -/

/-- **A name a typed component holds is a name.** -/
theorem nameOf_typed {free : FreeTypeContext} {bound : List TypeExpr} {component name : Pattern}
    (typed : HasType locatedCalc free bound component procType) (isName : nameOf component = some name) :
    HasType locatedCalc free bound name nameType := by
  cases component with
  | apply label arguments =>
      match arguments, isName with
      | [first, second, third], isName =>
          simp only [nameOf] at isName
          rcases triple_inv typed with ⟨isMarker, -, thirdTyped⟩ | ⟨listed, secondTyped, -⟩ | ⟨rfl, -, -⟩
          · rw [if_pos isMarker, Option.some.injEq] at isName
            subst isName
            exact thirdTyped
          · rw [if_neg (not_marker_of_capability listed), if_pos listed, Option.some.injEq] at isName
            subst isName
            exact secondTyped
          · simp [markers, capabilities] at isName
      | [], isName => simp [nameOf] at isName
      | [_], isName => simp [nameOf] at isName
      | [_, _], isName => simp [nameOf] at isName
      | _ :: _ :: _ :: _ :: _, isName => simp [nameOf] at isName
  | _ => simp [nameOf] at isName

/-- **A message a typed component holds is of a sort a communication sends.** -/
theorem messageOf_typed {free : FreeTypeContext} {bound : List TypeExpr} {component message : Pattern}
    (typed : HasType locatedCalc free bound component procType) (isMessageOf : messageOf component = some message) :
    ∃ sort : String, (sort = "Name" ∨ sort = "Cap") ∧ HasType locatedCalc free bound message (.base sort) := by
  cases component with
  | apply label arguments =>
      match arguments, isMessageOf with
      | [first, second, third], isMessageOf =>
          simp only [messageOf] at isMessageOf
          split_ifs at isMessageOf with isCap
          rw [Option.some.injEq] at isMessageOf
          subst isMessageOf isCap
          rcases triple_inv typed with ⟨isMarker, -, -⟩ | ⟨listed, -, -⟩ | ⟨-, secondTyped, -⟩
          · simp [markers] at isMarker
          · simp [capabilities] at listed
          · exact ⟨"Cap", .inr rfl, secondTyped⟩
      | [first, second], isMessageOf =>
          simp only [messageOf] at isMessageOf
          split_ifs at isMessageOf with isOutput
          rw [Option.some.injEq] at isMessageOf
          subst isMessageOf
          rcases (pair_inv typed).2 with ⟨sort, body, listed, -, -⟩ | ⟨sort, listed, messageTyped⟩
          · exact absurd isOutput (not_output_of_input (by
              simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at listed
              rcases listed with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> simp [inputs]))
          · simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at listed
            rcases listed with ⟨-, rfl⟩ | ⟨-, rfl⟩
            · exact ⟨_, .inl rfl, messageTyped⟩
            · exact ⟨_, .inr rfl, messageTyped⟩
      | [], isMessageOf => simp [messageOf] at isMessageOf
      | [_], isMessageOf => simp [messageOf] at isMessageOf
      | _ :: _ :: _ :: _ :: _, isMessageOf => simp [messageOf] at isMessageOf
  | _ => simp [messageOf] at isMessageOf

/-- What the assignment past a block's restrictions sends to one of them was that restriction. -/
theorem substitute_lift_eq_below {assignment : Assignment} {count index : Nat} {pattern : Pattern}
    (same : substitute (lift count assignment) pattern = .bvar index) (below : index < count) :
    pattern = .bvar index := by
  cases pattern with
  | bvar other =>
      by_cases otherBelow : other < count
      · rw [substitute_lift_below otherBelow] at same
        exact same
      · exfalso
        change lift count assignment other = .bvar index at same
        unfold Mettapedia.OSLF.MeTTaIL.ContextSubstitution.lift at same
        rw [if_neg otherBelow] at same
        exact lift_ne_below below same
  | fvar name => cases same
  | _ => simp [substitute] at same

/-- **A block's locations stay nested** when its outside receives an assignment. -/
theorem Nested.substituteOuter {count : Nat} {components : List Pattern} {assignment : Assignment}
    (messages : ∀ index, isMessage (assignment index) = true) (nested : Nested count components)
    (placesVariables : ∀ component ∈ components, ∀ index, placeAt component = some (.bvar index) →
      isVariable (lift count assignment index) = true) :
    Nested count (components.map (substitute (lift count assignment))) := by
  obtain ⟨depth, grows⟩ := nested
  refine ⟨depth, fun component member index child below childBelow isPlaced isChild => ?_⟩
  obtain ⟨original, inComponents, rfl⟩ := List.mem_map.mp member
  rw [placeAt_substitute (messages_liftN messages count) (placesVariables original inComponents)] at isPlaced
  rw [childOf_substitute (messages_liftN messages count)] at isChild
  obtain ⟨originalPlace, placeFound, placeIs⟩ := Option.map_eq_some_iff.mp isPlaced
  obtain ⟨originalChild, childFound, childIs⟩ := Option.map_eq_some_iff.mp isChild
  rw [substitute_lift_eq_below placeIs below] at placeFound
  rw [substitute_lift_eq_below childIs childBelow] at childFound
  exact grows original inComponents index child below childBelow placeFound childFound

variable {free : FreeTypeContext}

/-- **A well-located block whose outside receives an assignment is well-located**, when the assignment sends names
to variables and messages to messages, a variable to a location exactly when the variable is one, and a variable that
is no location to terms whose variables are no locations. -/
theorem WellLocated.substituteOuter {isLoc : Pattern → Prop} {place : Pattern} {form : Prenex}
    (well : WellLocated isLoc place form) :
    ∀ {assignment : Assignment} {isLoc' : Pattern → Prop} {bound : List TypeExpr},
      Members locatedCalc locatedBlock free (List.replicate form.count nameType ++ bound) form.components →
      (∀ index, isMessage (assignment index) = true) →
      (∀ index, bound[index]? = some nameType → isVariable (assignment index) = true) →
      (∀ pattern, isVariable pattern = true → (isLoc' (substitute assignment pattern) ↔ isLoc pattern)) →
      (∀ pattern, isVariable pattern = true → ¬ isLoc pattern →
        ∀ name ∈ messageVariables (substitute assignment pattern), ¬ isLoc' name) →
      LocVariables isLoc' → LocVariables isLoc →
      WellLocated isLoc' (substitute assignment place) (form.substituteOuter assignment) := by
  have signature : Mettapedia.GSLT.LanguageDef.RestrictionBlocks.BlockSignature locatedCalc locatedBlock :=
    Mettapedia.Languages.ProcessCalculi.Ambient.Located.locatedLanguage.toBlockSignature
  induction well with
  | @intro isLoc place count components placeLoc kinds placed unique names caps reps repsPlaced nested messages
      capConts bodies capsIH repsIH capContsIH bodiesIH =>
      intro assignment isLoc' bound typed messagesOf namesOf compat apart locVariables' locVariables
      have messagesL := messages_liftN messagesOf count
      have namesL := names_liftN namesOf count
      have sameMarked : ∀ index, Marked (components.map (substitute (lift count assignment))) index ↔
          Marked components index := fun _ => marked_substitute messagesOf kinds
      have compat' := insideLoc_substitute compat locVariables' sameMarked
      have apart' := insideLoc_apart apart sameMarked
      have innerVariables := insideLoc_locVariables isLoc count components
      have innerVariables' := insideLoc_locVariables isLoc' count (components.map (substitute (lift count assignment)))
      -- the places of the components receive variables
      have placesVariables : ∀ component ∈ components, ∀ at', placeAt component = some at' →
          isVariable (substitute (lift count assignment) at') = true := by
        intro component member at' sits
        rcases placed component member at' sits with same | ⟨index, below, rfl, -⟩
        · rw [same, substitute_lift_outer, isVariable_lift]
          exact locVariables' _ ((compat place (locVariables place placeLoc)).mpr placeLoc)
        · rw [substitute_lift_below below]
          rfl
      have placesOf : ∀ component ∈ components, placeAt (substitute (lift count assignment) component) =
          (placeAt component).map (substitute (lift count assignment)) := fun component member =>
        placeAt_substitute messagesL fun index sits => placesVariables component member _ sits
      simp only [Prenex.substituteOuter]
      refine .intro ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
      · exact (compat place (locVariables place placeLoc)).mpr placeLoc
      · intro component member
        obtain ⟨original, inComponents, rfl⟩ := List.mem_map.mp member
        cases kinds original inComponents with
        | @marker label parent name index isMarker below =>
            have shape : substitute (lift count assignment) (.apply label [parent, .bvar index, name]) =
                .apply label [substitute (lift count assignment) parent, .bvar index,
                  substitute (lift count assignment) name] := by
              simp only [substitute, substituteList_eq_map, List.map_cons, List.map_nil]
              rw [lift_apply_below below]
            rw [shape]
            exact .marker isMarker below
        | capability listed =>
            simp only [substitute, substituteList_eq_map, List.map_cons, List.map_nil]
            exact .capability listed
        | replication =>
            simp only [substitute, substituteList_eq_map, List.map_cons, List.map_nil]
            exact .replication
        | cap =>
            simp only [substitute, substituteList_eq_map, List.map_cons, List.map_nil]
            exact .cap
        | input listed =>
            simp only [substitute, substituteList_eq_map, List.map_cons, List.map_nil]
            exact .input listed
        | output listed =>
            simp only [substitute, substituteList_eq_map, List.map_cons, List.map_nil]
            exact .output listed
      · intro component member at' isPlaced
        obtain ⟨original, inComponents, rfl⟩ := List.mem_map.mp member
        rw [placesOf original inComponents] at isPlaced
        cases found : placeAt original with
        | none => rw [found] at isPlaced; cases isPlaced
        | some originalPlace =>
            rw [found, Option.map_some, Option.some.injEq] at isPlaced
            subst isPlaced
            rcases placed original inComponents originalPlace found with rfl | ⟨index, below, rfl, isMarked⟩
            · exact .inl (substitute_lift_outer assignment count place)
            · exact .inr ⟨index, below, substitute_lift_below below, (sameMarked index).mpr isMarked⟩
      · intro index
        rw [List.filter_map, List.length_map]
        refine le_trans (le_of_eq ?_) (unique index)
        congr 1
        apply List.filter_congr
        intro component member
        simp only [Function.comp, childOf_substitute messagesL]
        cases found : childOf component with
        | none => simp
        | some child =>
            simp only [Option.map_some]
            obtain ⟨childIndex, childBelow, rfl⟩ := childOf_bvar_of_kind (kinds component member) found
            rw [substitute_lift_below childBelow]
      · intro component member name isName
        obtain ⟨original, inComponents, rfl⟩ := List.mem_map.mp member
        rw [nameOf_substitute messagesL] at isName
        cases found : nameOf original with
        | none => rw [found] at isName; cases isName
        | some originalName =>
            rw [found, Option.map_some, Option.some.injEq] at isName
            subst isName
            obtain ⟨isVar, apartName⟩ := names original inComponents originalName found
            exact ⟨name_substitute namesL (nameOf_typed (typed original inComponents) found) isVar,
              fun inside => apartName ((compat' originalName isVar).mp inside)⟩
      · intro component member label at' name continuation isCapability listed
        obtain ⟨original, inComponents, rfl⟩ := List.mem_map.mp member
        cases original with
        | apply originalLabel arguments =>
            match arguments, isCapability with
            | [originalAt, originalName, originalContinuation], isCapability =>
                simp only [substitute, substituteList_eq_map, List.map_cons, List.map_nil, Pattern.apply.injEq,
                  List.cons.injEq, and_true] at isCapability
                obtain ⟨rfl, rfl, rfl, rfl⟩ := isCapability
                have continuationTyped : HasType locatedCalc free (List.replicate count nameType ++ bound)
                    originalContinuation procType := by
                  rcases triple_inv (typed _ inComponents) with ⟨isMarker, -, -⟩ | ⟨-, -, third⟩ | ⟨-, -, third⟩
                  · exact absurd listed (not_capability_of_marker isMarker)
                  · exact third
                  · exact third
                rw [decompose_substitute (messages_atomic messagesL)]
                exact capsIH _ inComponents _ _ _ _ rfl listed (decompose_sound continuationTyped).1 messagesL
                  namesL compat' apart' innerVariables' innerVariables
            | [], isCapability => simp [substitute] at isCapability
            | [_], isCapability => simp [substitute] at isCapability
            | [_, _], isCapability => simp [substitute] at isCapability
            | _ :: _ :: _ :: _ :: _, isCapability => simp [substitute] at isCapability
        | _ => exact absurd (kinds _ inComponents) fun kind => by cases kind
      · intro component member argument at' isRep isPlaced
        obtain ⟨original, inComponents, rfl⟩ := List.mem_map.mp member
        rw [placesOf original inComponents] at isPlaced
        cases found : placeAt original with
        | none => rw [found] at isPlaced; cases isPlaced
        | some originalPlace =>
            rw [found, Option.map_some, Option.some.injEq] at isPlaced
            subst isPlaced
            cases original with
            | apply originalLabel arguments =>
                match arguments, isRep with
                | [originalArgument], isRep =>
                    simp only [substitute, substituteList_eq_map, List.map_cons, List.map_nil, Pattern.apply.injEq,
                      List.cons.injEq, and_true] at isRep
                    obtain ⟨rfl, rfl⟩ := isRep
                    rw [decompose_substitute (messages_atomic messagesL)]
                    exact repsIH _ inComponents _ _ rfl found
                      (decompose_sound (rep_inv (typed _ inComponents))).1 messagesL namesL compat' apart'
                      innerVariables' innerVariables
                | [], isRep => simp [substitute] at isRep
                | _ :: _ :: _, isRep => simp [substitute] at isRep
            | _ => exact absurd (kinds _ inComponents) fun kind => by cases kind
      · intro component member argument isRep
        obtain ⟨original, inComponents, rfl⟩ := List.mem_map.mp member
        rw [placesOf original inComponents]
        cases original with
        | apply originalLabel arguments =>
            match arguments, isRep with
            | [originalArgument], isRep =>
                simp only [substitute, substituteList_eq_map, List.map_cons, List.map_nil, Pattern.apply.injEq,
                  List.cons.injEq, and_true] at isRep
                obtain ⟨rfl, -⟩ := isRep
                have isSome := repsPlaced _ inComponents originalArgument rfl
                cases found : placeAt (Pattern.apply "LRep" [originalArgument]) with
                | none => rw [found] at isSome; cases isSome
                | some at' => rfl
            | [], isRep => simp [substitute] at isRep
            | _ :: _ :: _, isRep => simp [substitute] at isRep
        | _ => exact absurd (kinds _ inComponents) fun kind => by cases kind
      · obtain ⟨depth, grows⟩ := nested
        exact Nested.substituteOuter messagesOf ⟨depth, grows⟩ fun component member index sits =>
          placesVariables component member _ sits
      · intro component member message isMessageOf
        obtain ⟨original, inComponents, rfl⟩ := List.mem_map.mp member
        rw [messageOf_substitute messagesL] at isMessageOf
        cases found : messageOf original with
        | none => rw [found] at isMessageOf; cases isMessageOf
        | some originalMessage =>
            rw [found, Option.map_some, Option.some.injEq] at isMessageOf
            subst isMessageOf
            obtain ⟨isMsg, apartMessage⟩ := messages original inComponents originalMessage found
            obtain ⟨sort, sorted, messageTyped⟩ := messageOf_typed (typed original inComponents) found
            refine ⟨message_substitute messagesL namesL sorted messageTyped isMsg, fun name inVariables => ?_⟩
            obtain ⟨held, inOriginal, inImage⟩ := messageVariables_substitute originalMessage inVariables
            exact apart' held (isVariable_of_messageVariables inOriginal) (apartMessage held inOriginal) name inImage
      · intro component member at' message continuation isCapComponent
        obtain ⟨original, inComponents, rfl⟩ := List.mem_map.mp member
        cases original with
        | apply originalLabel arguments =>
            match arguments, isCapComponent with
            | [originalAt, originalMessage, originalContinuation], isCapComponent =>
                simp only [substitute, substituteList_eq_map, List.map_cons, List.map_nil, Pattern.apply.injEq,
                  List.cons.injEq, and_true] at isCapComponent
                obtain ⟨rfl, rfl, rfl, rfl⟩ := isCapComponent
                have continuationTyped : HasType locatedCalc free (List.replicate count nameType ++ bound)
                    originalContinuation procType := by
                  rcases triple_inv (typed _ inComponents) with ⟨isMarker, -, -⟩ | ⟨listed, -, -⟩ | ⟨-, -, third⟩
                  · simp [markers] at isMarker
                  · simp [capabilities] at listed
                  · exact third
                rw [decompose_substitute (messages_atomic messagesL)]
                exact capContsIH _ inComponents _ _ _ rfl (decompose_sound continuationTyped).1 messagesL namesL
                  compat' apart' innerVariables' innerVariables
            | [], isCapComponent => simp [substitute] at isCapComponent
            | [_], isCapComponent => simp [substitute] at isCapComponent
            | [_, _], isCapComponent => simp [substitute] at isCapComponent
            | _ :: _ :: _ :: _ :: _, isCapComponent => simp [substitute] at isCapComponent
        | _ => exact absurd (kinds _ inComponents) fun kind => by cases kind
      · intro component member label at' binder body isInput listed
        obtain ⟨original, inComponents, rfl⟩ := List.mem_map.mp member
        cases original with
        | apply originalLabel arguments =>
            match arguments, isInput with
            | [originalAt, originalSecond], isInput =>
                cases originalSecond with
                | lambda originalBinder originalBody =>
                    simp only [substitute, substituteList_eq_map, List.map_cons, List.map_nil, Pattern.apply.injEq,
                      List.cons.injEq, Pattern.lambda.injEq, and_true] at isInput
                    obtain ⟨rfl, rfl, rfl, rfl⟩ := isInput
                    obtain ⟨sort, bodyTyped⟩ : ∃ sort : String, HasType locatedCalc free
                        (.base sort :: (List.replicate count nameType ++ bound)) originalBody procType := by
                      rcases (pair_inv (typed _ inComponents)).2 with ⟨sort, body', -, same, typed'⟩ | ⟨sort, listed', -⟩
                      · simp only [Pattern.lambda.injEq] at same
                        obtain ⟨-, rfl⟩ := same
                        exact ⟨sort, typed'⟩
                      · exact absurd listed (not_input_of_output (by
                          simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at listed'
                          rcases listed' with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> simp [outputs]))
                    rw [decompose_substitute (messages_atomic (messages_liftN messagesL 1)),
                      ← substitute_lift_outer (lift count assignment) 1 originalAt]
                    exact bodiesIH _ inComponents _ _ _ _ rfl listed (decompose_sound bodyTyped).1
                      (messages_liftN messagesL 1) (names_cons namesL _) (underName_substitute compat' innerVariables')
                      (underName_apart apart' innerVariables') (underName_locVariables _) (underName_locVariables _)
                | bvar other =>
                    simp only [substitute, substituteList_eq_map, List.map_cons, List.map_nil, Pattern.apply.injEq,
                      List.cons.injEq, and_true] at isInput
                    exact absurd isInput.2.2 (Mettapedia.Languages.ProcessCalculi.Ambient.Encoding.message_notLambda
                      (messagesL other) _ _)
                | _ => simp [substitute] at isInput
            | [], isInput => simp [substitute] at isInput
            | [_], isInput => simp [substitute] at isInput
            | _ :: _ :: _ :: _, isInput => simp [substitute] at isInput
        | _ => exact absurd (kinds _ inComponents) fun kind => by cases kind

/-- **An input's body, receiving a message whose variables are no locations, is a well-located block at the input's
place.** -/
theorem WellLocated.instantiate {isLoc : Pattern → Prop} {bound : List TypeExpr} {sort : TypeExpr}
    {place body message : Pattern}
    (well : WellLocated (underName isLoc) (liftBVars 0 1 place) (decompose locatedBlock body))
    (typed : HasType locatedCalc free (sort :: bound) body procType)
    (isMsg : isMessage message = true) (nameVar : sort = nameType → isVariable message = true)
    (apartMessage : ∀ name ∈ messageVariables message, ¬ isLoc name) (locVariables : LocVariables isLoc) :
    WellLocated isLoc place (decompose locatedBlock (instantiateBVar message body)) := by
  have signature : Mettapedia.GSLT.LanguageDef.RestrictionBlocks.BlockSignature locatedCalc locatedBlock :=
    Mettapedia.Languages.ProcessCalculi.Ambient.Located.locatedLanguage.toBlockSignature
  have placeIs : substitute (single message) (liftBVars 0 1 place) = place := by
    rw [← shiftName_eq_liftBVars, substitute_single_shiftName]
  have assigned := single_located (isLoc := isLoc) (bound := bound) isMsg nameVar
  have shaped := well.substituteOuter (assignment := single message) (isLoc' := isLoc) (bound := sort :: bound)
    (decompose_sound typed).1 assigned.messages assigned.names
    (fun pattern isVar => by
      cases pattern with
      | bvar index =>
          cases index with
          | zero =>
              simp only [underName, iff_false]
              intro isLocation
              have isLocation' : isLoc message := isLocation
              have messageVar := locVariables _ isLocation'
              refine apartMessage message ?_ isLocation'
              cases message with
              | bvar index => simp [messageVariables]
              | fvar name => simp [messageVariables]
              | _ => simp [isVariable] at messageVar
          | succ index => exact Iff.rfl
      | fvar name => exact Iff.rfl
      | _ => simp [isVariable] at isVar)
    (fun pattern isVar notLocation name member => by
      cases pattern with
      | bvar index =>
          cases index with
          | zero => exact apartMessage name member
          | succ index =>
              simp only [substitute, single, messageVariables, List.mem_singleton] at member
              subst member
              exact notLocation
      | fvar fname =>
          simp only [substitute, messageVariables, List.mem_singleton] at member
          subst member
          exact notLocation
      | _ => simp [isVariable] at isVar)
    locVariables (underName_locVariables isLoc)
  rw [placeIs] at shaped
  rwa [← substitute_single_eq_instantiateBVar, decompose_substitute (messages_atomic assigned.messages)]

/-- **A sublist of a well-located block's components keeping every location is well-located.** -/
theorem WellLocated.sublist_marked {isLoc : Pattern → Prop} {place : Pattern} {count : Nat}
    {components smaller : List Pattern} (well : WellLocated isLoc place ⟨count, components⟩)
    (sub : smaller.Sublist components) (markedSame : ∀ index, Marked smaller index ↔ Marked components index) :
    WellLocated isLoc place ⟨count, smaller⟩ := by
  have locSame : insideLoc isLoc count smaller = insideLoc isLoc count components := by
    funext pattern
    cases pattern with
    | bvar index =>
        simp only [insideLoc]
        split_ifs
        · exact propext (markedSame index)
        · rfl
    | _ => rfl
  have within : ∀ component ∈ smaller, component ∈ components := fun component member => sub.subset member
  cases well with
  | intro placeLoc kinds placed unique names caps reps repsPlaced nested messages capConts bodies =>
      refine .intro placeLoc (fun component member => kinds component (within component member))
        (fun component member at' sits => ?_) (fun index => le_trans (sub.filter _).length_le (unique index))
        (fun component member name isName => by
          rw [locSame]
          exact names component (within component member) name isName)
        (fun component member label at' name continuation isCapability listed => by
          rw [locSame]
          exact caps component (within component member) label at' name continuation isCapability listed)
        (fun component member argument at' isReplication sits => by
          rw [locSame]
          exact reps component (within component member) argument at' isReplication sits)
        (fun component member argument isReplication => repsPlaced component (within component member) argument
          isReplication)
        (nested.sublist within)
        (fun component member message isMsgOf => by
          rw [locSame]
          exact messages component (within component member) message isMsgOf)
        (fun component member at' message continuation isCapComponent => by
          rw [locSame]
          exact capConts component (within component member) at' message continuation isCapComponent)
        (fun component member label at' binder body isInput listed => by
          rw [locSame]
          exact bodies component (within component member) label at' binder body isInput listed)
      rcases placed component (within component member) at' sits with atRoot | ⟨index, below, same, isMarked⟩
      · exact .inl atRoot
      · exact .inr ⟨index, below, same, (markedSame index).mpr isMarked⟩

end Mettapedia.Languages.ProcessCalculi.Ambient.Decoding
