import Mettapedia.Languages.ProcessCalculi.Ambient.CommNormal
import Mettapedia.Languages.ProcessCalculi.Ambient.CommReflection
import Mettapedia.Languages.ProcessCalculi.Ambient.EncodingReacts
import Mettapedia.GSLT.LanguageDef.RestrictionBlocks.ObjectSubstitution

/-!
# Steps of ambients with communication: typing, substitution and the path normal form

- **Substitution**: a substitution of terms that are no abstractions keeps every shape of the laws
  (`AmbShape.substituted`, `CommShape.substituted`), so continuations related by the core's laws, or by the laws with
  paths, stay related once a typed message is received (`core_objectChain_instantiate`,
  `comm_objectChain_instantiate`).
- **Typing**: a step keeps a typed object process a typed object process (`commStep_typed`); a communication
  instantiates the input's body with a message of the input's sort.
- **The path normal form**: a step of a process is matched by a step of its path normal form, to a contractum
  equivalent by the laws with paths (`AmbCommRawStep.normal`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.Ambient.Comm

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Substitution (liftBVars instantiateBVar)
open Mettapedia.OSLF.MeTTaIL.ContextSubstitution (Assignment substitute lift single substituteList_eq_map
  substitute_single_eq_instantiateBVar)
open Mettapedia.GSLT.LanguageDef.WellSorted (HasType FreeTypeContext isObjectPattern isObjectPatternList)
open Mettapedia.GSLT.LanguageDef.BagNormalForm (isObjectPatternList_iff)
open Mettapedia.GSLT.LanguageDef.RestrictionBlocks (BaseContext ObjectChain ProcEquiv Members NoAbstractions
  NoAbstractions.single SortedAssignment substitute_lift_one isObject_substitute members_of_bag restrict_typed
  restrict_fill collection_congr size sizeList)
open Mettapedia.Languages.ProcessCalculi.Ambient.Full (AmbShape ambientBlock ambientShapes)
open Mettapedia.Languages.ProcessCalculi.Ambient.Encoding (nameType procType amb_inv prefix_inv input_inv output_inv
  name_cases_ambient)
open Mettapedia.Languages.ProcessCalculi.Ambient.Steps (step_typed bag_objects pair_objects bag_typed_of bag_object_of
  amb_object_of)
open Mettapedia.Languages.ProcessCalculi.Ambient.Mobile (amb)

/-! ## Substitution -/

/-- **A substitution of terms that are no abstractions keeps each shape of the core's laws.** -/
theorem AmbShape.substituted {assignment : Assignment} (plain : NoAbstractions assignment) {source target : Pattern}
    (shape : AmbShape source target) : AmbShape (substitute assignment source) (substitute assignment target) := by
  cases shape with
  | law shape => exact .law (shape.substituted assignment plain)
  | boundary name binder body =>
      simp only [substitute, substituteList_eq_map, List.map_cons, List.map_nil, substitute_lift_one]
      exact .boundary _ _ _
  | boundaryReverse name binder body =>
      simp only [substitute, substituteList_eq_map, List.map_cons, List.map_nil, substitute_lift_one]
      exact .boundaryReverse _ _ _

/-- **A substitution of terms that are no abstractions keeps each shape of the laws with paths.** -/
theorem CommShape.substituted {assignment : Assignment} (plain : NoAbstractions assignment) {source target : Pattern}
    (shape : CommShape source target) : CommShape (substitute assignment source) (substitute assignment target) := by
  cases shape with
  | core shape => exact .core (AmbShape.substituted plain shape)
  | path shape =>
      induction shape with
      | eps process =>
          simpa [substitute, substituteList_eq_map] using CommShape.path (.eps (substitute assignment process))
      | dot first rest process =>
          simpa [substitute, substituteList_eq_map] using
            CommShape.path (.dot (substitute assignment first) (substitute assignment rest) (substitute assignment process))
      | capPrefix listed name process =>
          simpa [substitute, substituteList_eq_map] using
            CommShape.path (.capPrefix listed (substitute assignment name) (substitute assignment process))

/-- **Receiving a typed message for the innermost variable** is an assignment of terms of the variables' sorts. -/
theorem single_sorted {language : LanguageDef} {free : FreeTypeContext} {bound : List TypeExpr} {message : Pattern}
    {sort : String} (messageTyped : HasType language free bound message (.base sort))
    (messageObject : isObjectPattern message = true) :
    SortedAssignment language free (.base sort :: bound) bound (single message) where
  typed index type lookup := by
    cases index with
    | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at lookup
        subst lookup
        exact messageTyped
    | succ index => exact HasType.bvar (by simpa using lookup)
  objects index := by
    cases index with
    | zero => exact messageObject
    | succ => rfl

/-- **Continuations related by the core's laws stay related once a typed message is received.** -/
theorem core_objectChain_instantiate {free : FreeTypeContext} {bound : List TypeExpr} (context : BaseContext free bound)
    {message : Pattern} {sort : String} (messageTyped : HasType ambientCoreCalc free bound message (.base sort))
    (messageObject : isObjectPattern message = true) (notLambda : ∀ binder body, message ≠ .lambda binder body)
    {first second : Pattern} (chain : ObjectChain ambientCoreCalc free (.base sort :: bound) procType first second) :
    ObjectChain ambientCoreCalc free bound procType (instantiateBVar message first) (instantiateBVar message second) := by
  rw [← substitute_single_eq_instantiateBVar, ← substitute_single_eq_instantiateBVar]
  exact ambientShapes.objectChain_substitute (fun plain shape => AmbShape.substituted plain shape) context
    (single_sorted messageTyped messageObject) (NoAbstractions.single notLambda) chain

/-- **Continuations related by the laws with paths stay related once a typed message is received.** -/
theorem comm_objectChain_instantiate {free : FreeTypeContext} {bound : List TypeExpr} (context : BaseContext free bound)
    {message : Pattern} {sort : String} (messageTyped : HasType ambientCommCalc free bound message (.base sort))
    (messageObject : isObjectPattern message = true) (notLambda : ∀ binder body, message ≠ .lambda binder body)
    {first second : Pattern} (chain : ObjectChain ambientCommCalc free (.base sort :: bound) procType first second) :
    ObjectChain ambientCommCalc free bound procType (instantiateBVar message first) (instantiateBVar message second) := by
  rw [← substitute_single_eq_instantiateBVar, ← substitute_single_eq_instantiateBVar]
  exact commShapes.objectChain_substitute (fun plain shape => CommShape.substituted plain shape) context
    (single_sorted messageTyped messageObject) (NoAbstractions.single notLambda) chain

/-! ## Typing -/

/-- The sorts an input binds and an output sends, by channel. -/
theorem channels_sort {input output : String} (listed : (input, output) ∈ channels) :
    ∃ sort, (input, sort) ∈ [("AInName", "Name"), ("AInCap", "Cap")] ∧
      (output, sort) ∈ [("AOutName", "Name"), ("AOutCap", "Cap")] := by
  simp only [channels, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at listed
  rcases listed with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact ⟨"Name", by simp, by simp⟩
  · exact ⟨"Cap", by simp, by simp⟩

/-- **A communication between typed object processes**: the body is typed under the message's sort, the message is a
typed object, and the reception is a typed object process. -/
theorem comm_parts {free : FreeTypeContext} {bound : List TypeExpr} {input output : String}
    (listed : (input, output) ∈ channels) {binder : Option String} {body message : Pattern}
    (inputTyped : HasType ambientCoreCalc free bound (.apply input [.lambda binder body]) procType)
    (inputObject : isObjectPattern (.apply input [.lambda binder body]) = true)
    (outputTyped : HasType ambientCoreCalc free bound (.apply output [message]) procType)
    (outputObject : isObjectPattern (.apply output [message]) = true) :
    ∃ sort, binder = none ∧ HasType ambientCoreCalc free (.base sort :: bound) body procType ∧
      HasType ambientCoreCalc free bound message (.base sort) ∧ isObjectPattern body = true ∧
      isObjectPattern message = true ∧
      HasType ambientCoreCalc free bound (instantiateBVar message body) procType ∧
      isObjectPattern (instantiateBVar message body) = true := by
  obtain ⟨sort, inputListed, outputListed⟩ := channels_sort listed
  obtain ⟨rfl, bodyTyped⟩ := input_inv inputListed inputTyped
  have messageTyped := output_inv outputListed outputTyped
  have bodyObject : isObjectPattern body = true := by
    simpa [isObjectPattern, isObjectPatternList] using inputObject
  have messageObject : isObjectPattern message = true := by
    simpa [isObjectPattern, isObjectPatternList] using outputObject
  have assigned := single_sorted messageTyped messageObject
  refine ⟨sort, rfl, bodyTyped, messageTyped, bodyObject, messageObject, ?_, ?_⟩
  · rw [← substitute_single_eq_instantiateBVar]
    exact HasType.substituteBoundOnSupport bodyTyped _ fun index type _ lookup => assigned.typed index type lookup
  · rw [← substitute_single_eq_instantiateBVar]
    exact isObject_substitute _ assigned.objects bodyObject

/-- **A step keeps a typed object process a typed object process.** -/
theorem commStep_typed {free : FreeTypeContext} {source target : Pattern} (step : AmbCommRawStep source target) :
    ∀ {bound : List TypeExpr}, HasType ambientCoreCalc free bound source procType →
      isObjectPattern source = true →
      HasType ambientCoreCalc free bound target procType ∧ isObjectPattern target = true := by
  induction step with
  | «open» i hi j hj name process content capability boundary =>
      exact step_typed (.open i hi j hj name process content capability boundary)
  | enter i hi j hj name target process host k hk mover capability destination =>
      exact step_typed (.enter i hi j hj name target process host k hk mover capability destination)
  | exit i hi name parent process k hk mover capability =>
      exact step_typed (.exit i hi name parent process k hk mover capability)
  | @comm elements tail input output listed i hi j hj binder body message receiving sending =>
      intro bound typed object
      obtain ⟨rfl, objects⟩ := bag_objects object
      have members := members_of_bag (language := ambientCoreCalc) (block := ambientBlock) typed
      have inputTyped := members _ (List.getElem_mem hi)
      have inputObject := objects _ (List.getElem_mem hi)
      rw [receiving] at inputTyped inputObject
      have outputTyped := members _ (List.mem_of_mem_eraseIdx (List.getElem_mem hj))
      have outputObject := objects _ (List.mem_of_mem_eraseIdx (List.getElem_mem hj))
      rw [sending] at outputTyped outputObject
      obtain ⟨sort, -, -, -, -, -, receivedTyped, receivedObject⟩ :=
        comm_parts listed inputTyped inputObject outputTyped outputObject
      refine ⟨bag_typed_of fun element member => ?_, bag_object_of fun element member => ?_⟩
      · rcases List.mem_cons.mp member with rfl | inRest
        · exact receivedTyped
        · exact members element (List.mem_of_mem_eraseIdx (List.mem_of_mem_eraseIdx inRest))
      · rcases List.mem_cons.mp member with rfl | inRest
        · exact receivedObject
        · exact objects element (List.mem_of_mem_eraseIdx (List.mem_of_mem_eraseIdx inRest))
  | @par elements tail i hi target inner recurse =>
      intro bound typed object
      obtain ⟨rfl, objects⟩ := bag_objects object
      have members := members_of_bag (language := ambientCoreCalc) (block := ambientBlock) typed
      obtain ⟨steppedTyped, steppedObject⟩ := recurse (members _ (List.getElem_mem hi)) (objects _ (List.getElem_mem hi))
      refine ⟨bag_typed_of fun element member => ?_, bag_object_of fun element member => ?_⟩
      · rcases List.mem_cons.mp member with rfl | inRest
        · exact steppedTyped
        · exact members element (List.mem_of_mem_eraseIdx inRest)
      · rcases List.mem_cons.mp member with rfl | inRest
        · exact steppedObject
        · exact objects element (List.mem_of_mem_eraseIdx inRest)
  | @res binder source target inner recurse =>
      intro bound typed object
      obtain ⟨bodyTyped, -, rfl⟩ := coreSignature.restriction_typed typed
      have bodyObject : isObjectPattern source = true := by simpa [isObjectPattern, isObjectPatternList] using object
      obtain ⟨steppedTyped, steppedObject⟩ := recurse bodyTyped bodyObject
      exact ⟨restrict_typed (block := ambientBlock) steppedTyped, by simpa [isObjectPattern, isObjectPatternList]
        using steppedObject⟩
  | @ambient name content target inner recurse =>
      intro bound typed object
      obtain ⟨nameTyped, contentTyped⟩ := amb_inv typed
      obtain ⟨nameObject, contentObject⟩ := pair_objects object
      obtain ⟨steppedTyped, steppedObject⟩ := recurse contentTyped contentObject
      exact ⟨Mettapedia.Languages.ProcessCalculi.Ambient.Full.amb_typed nameTyped steppedTyped,
        amb_object_of nameObject steppedObject⟩

/-! ## Steps in path normal form -/

/-- A typed object process is equivalent to its path normal form, read back. -/
theorem normal_equivalent {free : FreeTypeContext} {bound : List TypeExpr} {process : Pattern}
    (typed : HasType ambientCoreCalc free bound process procType) (object : isObjectPattern process = true) :
    ProcEquiv ambientCommCalc ambientBlock free bound (pathNF process) process :=
  .symm _ _ (pathNF_equivalent (size process + 1) (Nat.lt_succ_self _) (typed.of_terms_subset core_terms_comm) object)

/-- **Each member of a typed bag of object processes is equivalent to its normal form.** -/
theorem normal_members {free : FreeTypeContext} {bound : List TypeExpr} {elements : List Pattern}
    (members : Members ambientCoreCalc ambientBlock free bound elements)
    (objects : ∀ element ∈ elements, isObjectPattern element = true) :
    List.Forall₂ (ProcEquiv ambientCommCalc ambientBlock free bound) (elements.map pathNF) elements :=
  List.forall₂_map_left_iff.mpr (List.forall₂_same.mpr fun element member =>
    normal_equivalent (members element member) (objects element member))

/-- The normal forms of the members of a typed bag of object processes are typed. -/
theorem normal_members_typed {free : FreeTypeContext} {bound : List TypeExpr} {elements : List Pattern}
    (members : Members ambientCoreCalc ambientBlock free bound elements)
    (objects : ∀ element ∈ elements, isObjectPattern element = true) :
    Members ambientCommCalc ambientBlock free bound (elements.map pathNF) := by
  intro element member
  obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp member
  exact (pathNF_typed (members original originalMember) (objects original originalMember)).of_terms_subset
    core_terms_comm

/-- **A step of a typed object process is matched by a step of its path normal form**, to a contractum equivalent by
the laws with paths. -/
theorem AmbCommRawStep.normal {free : FreeTypeContext} {source target : Pattern} (step : AmbCommRawStep source target) :
    ∀ {bound : List TypeExpr}, BaseContext free bound → HasType ambientCoreCalc free bound source procType →
      isObjectPattern source = true →
      ∃ target', AmbCommRawStep (pathNF source) target' ∧
        ProcEquiv ambientCommCalc ambientBlock free bound target' target := by
  induction step with
  | @«open» elements tail i hi j hj name process content capability boundary =>
      intro bound context typed object
      obtain ⟨targetTyped, targetObject⟩ :=
        commStep_typed (.open i hi j hj name process content capability boundary) typed object
      refine ⟨_, ?_, normal_equivalent targetTyped targetObject⟩
      have stepped := AmbCommRawStep.open (elements := elements.map pathNF) (tail := tail) i (by simpa using hi) j
        (by simpa [List.eraseIdx_map] using hj) (pathNF name) (pathNF process) (pathNF content)
        (by simp [capability]) (by simp [List.eraseIdx_map, boundary, amb])
      simpa [List.eraseIdx_map] using stepped
  | @enter elements tail i hi j hj name target process host inner innerTail k hk mover capability destination =>
      intro bound context typed object
      obtain ⟨targetTyped, targetObject⟩ :=
        commStep_typed (.enter i hi j hj name target process host k hk mover capability destination) typed object
      refine ⟨_, ?_, normal_equivalent targetTyped targetObject⟩
      have stepped := AmbCommRawStep.enter (elements := elements.map pathNF) (tail := tail) (inner := inner.map pathNF)
        (innerTail := innerTail) i (by simpa using hi) j (by simpa [List.eraseIdx_map] using hj)
        (pathNF name) (pathNF target) (pathNF process) (pathNF host) k (by simpa using hk)
        (by simp [mover, amb]) (by simp [capability])
        (by simp [List.eraseIdx_map, destination, amb])
      simpa [List.eraseIdx_map, amb] using stepped
  | @exit contents tail i hi name parent process inner innerTail k hk mover capability =>
      intro bound context typed object
      obtain ⟨targetTyped, targetObject⟩ :=
        commStep_typed (.exit i hi name parent process k hk mover capability) typed object
      refine ⟨_, ?_, normal_equivalent targetTyped targetObject⟩
      have stepped := AmbCommRawStep.exit (contents := contents.map pathNF) (tail := tail) (inner := inner.map pathNF)
        (innerTail := innerTail) i (by simpa using hi) (pathNF name) (pathNF parent) (pathNF process) k
        (by simpa using hk) (by simp [mover, amb]) (by simp [capability])
      simpa [List.eraseIdx_map, amb] using stepped
  | @comm elements tail input output listed i hi j hj binder body message receiving sending =>
      intro bound context typed object
      obtain ⟨rfl, objects⟩ := bag_objects object
      have members := members_of_bag (language := ambientCoreCalc) (block := ambientBlock) typed
      have inputTyped := members _ (List.getElem_mem hi)
      have inputObject := objects _ (List.getElem_mem hi)
      rw [receiving] at inputTyped inputObject
      have outputTyped := members _ (List.mem_of_mem_eraseIdx (List.getElem_mem hj))
      have outputObject := objects _ (List.mem_of_mem_eraseIdx (List.getElem_mem hj))
      rw [sending] at outputTyped outputObject
      obtain ⟨sort, inputListed, outputListed⟩ := channels_sort listed
      obtain ⟨rfl, bodyTyped⟩ := input_inv inputListed inputTyped
      have messageTyped := output_inv outputListed outputTyped
      have bodyObject : isObjectPattern body = true := by
        simpa [isObjectPattern, isObjectPatternList] using inputObject
      have messageObject : isObjectPattern message = true := by
        simpa [isObjectPattern, isObjectPatternList] using outputObject
      have sortContext : BaseContext free (.base sort :: bound) := context.cons sort
      have messageNormal : pathNF message = message := by
        simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at inputListed
        rcases inputListed with ⟨-, rfl⟩ | ⟨-, rfl⟩
        · exact pathNF_name messageTyped messageObject
        · exact pathNF_capability (size message + 1) (Nat.lt_succ_self _)
            (messageTyped.of_terms_subset core_terms_comm) messageObject
      have normalBodyTyped := pathNF_typed bodyTyped bodyObject
      have normalBodyObject := isObject_pathNF _ bodyObject
      have notLambda : ∀ binder' body', message ≠ .lambda binder' body' := fun _ _ same => by
        subst same
        cases messageTyped
      have bodyChain : ObjectChain ambientCommCalc free (.base sort :: bound) procType (pathNF body) body :=
        comm_objectChain sortContext (normal_equivalent bodyTyped bodyObject) normalBodyObject bodyObject
      have receivedRelated : ProcEquiv ambientCommCalc ambientBlock free bound
          (instantiateBVar message (pathNF body)) (instantiateBVar message body) :=
        (comm_objectChain_instantiate context (messageTyped.of_terms_subset core_terms_comm) messageObject notLambda
          bodyChain).toSortedEquiv
      have assigned := single_sorted messageTyped messageObject
      have normalReceivedTyped : HasType ambientCoreCalc free bound (instantiateBVar message (pathNF body)) procType := by
        rw [← substitute_single_eq_instantiateBVar]
        exact HasType.substituteBoundOnSupport normalBodyTyped _ fun index type _ lookup => assigned.typed index type lookup
      have restMembers : Members ambientCoreCalc ambientBlock free bound ((elements.eraseIdx i).eraseIdx j) :=
        fun element member => members element (List.mem_of_mem_eraseIdx (List.mem_of_mem_eraseIdx member))
      have restObjects : ∀ element ∈ (elements.eraseIdx i).eraseIdx j, isObjectPattern element = true :=
        fun element member => objects element (List.mem_of_mem_eraseIdx (List.mem_of_mem_eraseIdx member))
      have labelsNe : input ≠ "ACap" ∧ output ≠ "ACap" := by
        simp only [channels, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at listed
        rcases listed with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
      have stepped := AmbCommRawStep.comm (elements := elements.map pathNF) (tail := none) listed i (by simpa using hi) j
        (by simpa [List.eraseIdx_map] using hj) none (pathNF body) message
        (by simp [receiving, labelsNe.1])
        (by simp [List.eraseIdx_map, sending, messageNormal, labelsNe.2])
      rw [List.eraseIdx_map, List.eraseIdx_map] at stepped
      refine ⟨_, by simpa using stepped, ?_⟩
      have firstMembers : Members ambientCommCalc ambientBlock free bound
          (instantiateBVar message (pathNF body) :: ((elements.eraseIdx i).eraseIdx j).map pathNF) := by
        intro element member
        rcases List.mem_cons.mp member with rfl | inRest
        · exact normalReceivedTyped.of_terms_subset core_terms_comm
        · exact normal_members_typed restMembers restObjects element inRest
      exact collection_congr (language := ambientCommCalc) (block := ambientBlock) none firstMembers
        (.cons receivedRelated (normal_members restMembers restObjects)) [] Members.nil
  | @par elements tail i hi stepTarget inner recurse =>
      intro bound context typed object
      obtain ⟨rfl, objects⟩ := bag_objects object
      have members := members_of_bag (language := ambientCoreCalc) (block := ambientBlock) typed
      obtain ⟨target', stepped, related⟩ :=
        recurse context (members _ (List.getElem_mem hi)) (objects _ (List.getElem_mem hi))
      have restMembers : Members ambientCoreCalc ambientBlock free bound (elements.eraseIdx i) :=
        fun element member => members element (List.mem_of_mem_eraseIdx member)
      have restObjects : ∀ element ∈ elements.eraseIdx i, isObjectPattern element = true :=
        fun element member => objects element (List.mem_of_mem_eraseIdx member)
      obtain ⟨normalTyped, normalObject⟩ := pathNF_typed (members _ (List.getElem_mem hi)) (objects _ (List.getElem_mem hi)),
        isObject_pathNF _ (objects _ (List.getElem_mem hi))
      obtain ⟨target'Typed, -⟩ := commStep_typed stepped normalTyped normalObject
      rw [pathNF_collection]
      refine ⟨_, AmbCommRawStep.par (elements := elements.map pathNF) (tail := none) i (by simpa using hi)
        (by rw [List.getElem_map]; exact stepped), ?_⟩
      rw [List.eraseIdx_map]
      have firstMembers : Members ambientCommCalc ambientBlock free bound (target' :: (elements.eraseIdx i).map pathNF) := by
        intro element member
        rcases List.mem_cons.mp member with rfl | inRest
        · exact target'Typed.of_terms_subset core_terms_comm
        · exact normal_members_typed restMembers restObjects element inRest
      exact collection_congr (language := ambientCommCalc) (block := ambientBlock) none firstMembers
        (.cons related (normal_members restMembers restObjects)) [] Members.nil
  | @res binder source stepTarget inner recurse =>
      intro bound context typed object
      obtain ⟨bodyTyped, -, rfl⟩ := coreSignature.restriction_typed typed
      have bodyObject : isObjectPattern source = true := by simpa [isObjectPattern, isObjectPatternList] using object
      obtain ⟨target', stepped, related⟩ := recurse (context.cons "Name") bodyTyped bodyObject
      refine ⟨.apply "ANu" [.lambda none target'], ?_,
        restrict_fill (language := ambientCommCalc) (block := ambientBlock) related⟩
      simpa using AmbCommRawStep.res none stepped
  | @ambient name content stepTarget inner recurse =>
      intro bound context typed object
      obtain ⟨nameTyped, contentTyped⟩ := amb_inv typed
      obtain ⟨nameObject, contentObject⟩ := pair_objects object
      obtain ⟨target', stepped, related⟩ := recurse context contentTyped contentObject
      have nameNormal := pathNF_name nameTyped nameObject
      refine ⟨amb name target', ?_, amb_fill (nameTyped.of_terms_subset core_terms_comm) related⟩
      simpa [amb, nameNormal] using AmbCommRawStep.ambient name stepped

end Mettapedia.Languages.ProcessCalculi.Ambient.Comm
