import Mettapedia.Languages.ProcessCalculi.Ambient.LocatedSteps
import Mettapedia.Languages.ProcessCalculi.Ambient.FullReflection

/-!
# The located form of a step

A step of an ambient process is, in located form, a reaction of located atoms at the front of a block: the parts of
an entering, a leaving or an opening beside the rest, under the restrictions of the locations and names on the way. A
step inside a bag is a reaction at the front of the bag's block (`reacts_par`), a step under a restriction one more
restriction around it (`reacts_res`), and a step inside an ambient a reaction at the front of the block at the
ambient's location, beside the ambient's marker (`reacts_ambient`); what the step leaves stands where the step stood.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.Ambient.Steps

open Mettapedia.Languages.ProcessCalculi.Ambient.Comm (ambientCoreCalc coreSignature)

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine (RelationEnv)
open Mettapedia.OSLF.MeTTaIL.ContextualStep (engineBasePremises)
open Mettapedia.GSLT.LanguageDef.EquationSemantics (EquationEquiv)
open Mettapedia.GSLT.LanguageDef.WellSorted (HasType FreeTypeContext isObjectPattern isObjectPatternList)
open Mettapedia.GSLT.LanguageDef.RestrictionBlocks (ReactsAt ReplicationStepAt ReplicationReactions Members rename
  bag_perm_equivalent)
open Mettapedia.Languages.ProcessCalculi.Ambient.Located (locatedCalc locatedBlock locatedRepBlock locatedLanguage)
open Mettapedia.Languages.ProcessCalculi.Ambient.Encoding (nameType procType encode shiftName encode_bag encode_nu
  encode_amb)

variable {free : FreeTypeContext}

/-- **A reaction of equivalent terms**: replacing the source and the target by equivalent ones. -/
theorem ReactsAt.congr {bound : List TypeExpr} {source source' target target' : Pattern} {count : Nat}
    {parts result rest : List Pattern}
    (reacts : ReactsAt locatedCalc locatedBlock free bound source target count parts result rest)
    (sourceSame : EquationEquiv (engineBasePremises RelationEnv.empty) locatedCalc source' source)
    (targetSame : EquationEquiv (engineBasePremises RelationEnv.empty) locatedCalc target' target) :
    ReactsAt locatedCalc locatedBlock free bound source' target' count parts result rest :=
  ⟨reacts.members, reacts.objects, .trans _ _ _ sourceSame reacts.source, .trans _ _ _ targetSame reacts.target⟩

/-- **A step inside a bag** is a reaction at the front of the bag's block. -/
theorem reacts_par {reactions : ReplicationReactions locatedCalc locatedRepBlock LocStep} {bound : List TypeExpr}
    {relabel : Nat → Nat} {here : Pattern} {elements : List Pattern}
    {position : Nat} (inside : position < elements.length) {target : Pattern}
    (typed : HasType locatedCalc free bound (.collection .hashBag (elements.map (encode relabel here)) none) procType)
    (objects : ∀ element ∈ elements.map (encode relabel here), isObjectPattern element = true)
    (inner : ∃ count redex rest, ReplicationStepAt reactions free bound
      (encode relabel here elements[position]) target count redex rest) :
    ∃ count redex rest, ReplicationStepAt reactions free bound
      (encode relabel here (.collection .hashBag elements none))
      (.collection .hashBag (target :: (elements.eraseIdx position).map (encode relabel here)) none)
      count redex rest := by
  have signature : Mettapedia.GSLT.LanguageDef.RestrictionBlocks.BlockSignature locatedCalc
      locatedRepBlock.toBlock := locatedLanguage.toBlockSignature
  obtain ⟨count, redex, rest, reached⟩ := inner
  have mappedInside : position < (elements.map (encode relabel here)).length := by simpa using inside
  have reachedAt : ReplicationStepAt reactions free bound (elements.map (encode relabel here))[position]
      target count redex rest := by simpa using reached
  have lifted := ReactsAt.inBag position mappedInside (reactions.result_members redex) typed objects reachedAt
  rw [encode_bag, ← List.eraseIdx_map]
  exact ⟨count, redex, _, lifted⟩

/-- **A step under a restriction** is a reaction under one more restriction. -/
theorem reacts_res {reactions : ReplicationReactions locatedCalc locatedRepBlock LocStep} {bound : List TypeExpr}
    {relabel : Nat → Nat} {here source target : Pattern}
    (inner : ∃ count redex rest, ReplicationStepAt reactions free (nameType :: bound)
      (encode (Mettapedia.OSLF.MeTTaIL.CanonicalBags.liftIndex 1 relabel) (shiftName here) source) target
      count redex rest) :
    ∃ count redex rest, ReplicationStepAt reactions free bound
      (encode relabel here (.apply "ANu" [.lambda none source])) (.apply "LNu" [.lambda none target])
      count redex rest := by
  obtain ⟨count, redex, rest, reached⟩ := inner
  refine ⟨count + 1, redex, rest, ?_⟩
  rw [encode_nu]
  exact ReactsAt.restrict reached

/-- **A step inside an ambient** is a reaction at the front of the block at the ambient's location, beside its
marker. -/
theorem reacts_ambient {reactions : ReplicationReactions locatedCalc locatedRepBlock LocStep} {bound : List TypeExpr}
    {relabel : Nat → Nat} {here name content target : Pattern}
    (markerTyped : HasType locatedCalc free (nameType :: bound)
      (.apply "LAmb" [shiftName here, .bvar 0, rename (Nat.succ ∘ relabel) name]) procType)
    (markerObject : isObjectPattern (.apply "LAmb" [shiftName here, .bvar 0, rename (Nat.succ ∘ relabel) name]) =
      true)
    (contentTyped : HasType locatedCalc free (nameType :: bound) (encode (Nat.succ ∘ relabel) (.bvar 0) content)
      procType)
    (contentObject : isObjectPattern (encode (Nat.succ ∘ relabel) (.bvar 0) content) = true)
    (targetTyped : HasType locatedCalc free (nameType :: bound) target procType)
    (inner : ∃ count redex rest, ReplicationStepAt reactions free (nameType :: bound)
      (encode (Nat.succ ∘ relabel) (.bvar 0) content) target count redex rest) :
    ∃ count redex rest, ReplicationStepAt reactions free bound
      (encode relabel here (.apply "AAmb" [name, content]))
      (.apply "LNu" [.lambda none (.collection .hashBag
        [.apply "LAmb" [shiftName here, .bvar 0, rename (Nat.succ ∘ relabel) name], target] none)])
      count redex rest := by
  have signature : Mettapedia.GSLT.LanguageDef.RestrictionBlocks.BlockSignature locatedCalc
      locatedRepBlock.toBlock := locatedLanguage.toBlockSignature
  obtain ⟨count, redex, rest, reached⟩ := inner
  set marker := Pattern.apply "LAmb" [shiftName here, .bvar 0, rename (Nat.succ ∘ relabel) name] with markerIs
  have twoMembers : ∀ {process : Pattern},
      HasType locatedCalc free (nameType :: bound) process procType →
      Members locatedCalc locatedBlock free (nameType :: bound) [process, marker] := by
    intro process processTyped element member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact processTyped
    · exact markerTyped
  have swapped : ∀ {process : Pattern}, HasType locatedCalc free (nameType :: bound) process procType →
      EquationEquiv (engineBasePremises RelationEnv.empty) locatedCalc
        (.collection .hashBag [marker, process] none) (.collection .hashBag [process, marker] none) := by
    intro process processTyped
    have members := twoMembers processTyped
    exact (bag_perm_equivalent (language := locatedCalc) (block := locatedRepBlock)
      (fun element member => members element ((List.Perm.swap _ _ []).subset member))
      (List.Perm.swap _ _ [])).toEquationEquiv
  have pairTyped := signature.bag_typed (rest := none)
    (Mettapedia.GSLT.LanguageDef.BagNormalForm.elementsHaveType_iff.mpr (twoMembers contentTyped))
  have pairObjects : ∀ element ∈ [encode (Nat.succ ∘ relabel) (.bvar 0) content, marker],
      isObjectPattern element = true := by
    intro element member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact contentObject
    · exact markerObject
  have lifted := ReactsAt.inBag 0 (by simp) (reactions.result_members redex) pairTyped pairObjects
    (by simpa using reached)
  simp only [List.eraseIdx_cons_zero] at lifted
  have reordered := ReactsAt.congr lifted (swapped contentTyped) (swapped targetTyped)
  rw [encode_amb]
  exact ⟨count + 1, redex, _, ReactsAt.restrict reordered⟩


/-! ## Steps keep typed object processes -/

open Mettapedia.GSLT.LanguageDef.BagNormalForm (elementsHaveType_iff isObjectPatternList_iff)
open Mettapedia.GSLT.LanguageDef.RestrictionBlocks (members_of_bag restrict_typed)
open Mettapedia.Languages.ProcessCalculi.Ambient.Full (AmbNuRawStep ambientBlock
  amb_typed)
open Mettapedia.Languages.ProcessCalculi.Ambient.Encoding (amb_inv prefix_inv)

theorem bag_objects {elements : List Pattern} {tail : Option String}
    (object : isObjectPattern (.collection .hashBag elements tail) = true) :
    tail = none ∧ ∀ element ∈ elements, isObjectPattern element = true := by
  simp only [isObjectPattern, Bool.and_eq_true, isObjectPatternList_iff, Option.isNone_iff_eq_none] at object
  exact object

theorem pair_objects {label : String} {first second : Pattern}
    (object : isObjectPattern (.apply label [first, second]) = true) :
    isObjectPattern first = true ∧ isObjectPattern second = true := by
  simpa [isObjectPattern, isObjectPatternList] using object

theorem bag_typed_of {bound : List TypeExpr} {elements : List Pattern}
    (members : Members ambientCoreCalc ambientBlock free bound elements) :
    HasType ambientCoreCalc free bound (.collection .hashBag elements none) procType :=
  coreSignature.bag_typed (rest := none) (elementsHaveType_iff.mpr members)

theorem bag_object_of {elements : List Pattern} (objects : ∀ element ∈ elements, isObjectPattern element = true) :
    isObjectPattern (.collection .hashBag elements none) = true := by
  simpa [isObjectPattern, isObjectPatternList_iff] using objects

theorem amb_object_of {name content : Pattern} (nameObject : isObjectPattern name = true)
    (contentObject : isObjectPattern content = true) : isObjectPattern (.apply "AAmb" [name, content]) = true := by
  simp [isObjectPattern, isObjectPatternList, nameObject, contentObject]

/-- **A step keeps a typed object process a typed object process.** -/
theorem step_typed {source target : Pattern} (step : AmbNuRawStep source target) :
    ∀ {bound : List TypeExpr}, HasType ambientCoreCalc free bound source procType →
      isObjectPattern source = true →
      HasType ambientCoreCalc free bound target procType ∧ isObjectPattern target = true := by
  induction step with
  | @«open» elements tail i hi j hj name process content capability boundary =>
      intro bound typed object
      obtain ⟨rfl, objects⟩ := bag_objects object
      have members := members_of_bag (language := ambientCoreCalc) (block := ambientBlock) typed
      have capabilityTyped := members _ (List.getElem_mem hi)
      have capabilityObject := objects _ (List.getElem_mem hi)
      rw [capability] at capabilityTyped capabilityObject
      have boundaryTyped := members _ (List.mem_of_mem_eraseIdx (List.getElem_mem hj))
      have boundaryObject := objects _ (List.mem_of_mem_eraseIdx (List.getElem_mem hj))
      rw [boundary] at boundaryTyped boundaryObject
      obtain ⟨-, processTyped⟩ := prefix_inv (by simp) capabilityTyped
      obtain ⟨-, contentTyped⟩ := amb_inv boundaryTyped
      obtain ⟨-, processObject⟩ := pair_objects capabilityObject
      obtain ⟨-, contentObject⟩ := pair_objects boundaryObject
      refine ⟨bag_typed_of fun element member => ?_, bag_object_of fun element member => ?_⟩
      · simp only [List.mem_cons] at member
        rcases member with rfl | rfl | inRest
        · exact processTyped
        · exact contentTyped
        · exact members element (List.mem_of_mem_eraseIdx (List.mem_of_mem_eraseIdx inRest))
      · simp only [List.mem_cons] at member
        rcases member with rfl | rfl | inRest
        · exact processObject
        · exact contentObject
        · exact objects element (List.mem_of_mem_eraseIdx (List.mem_of_mem_eraseIdx inRest))
  | @enter elements tail i hi j hj name target process host inner innerTail k hk mover capability destination =>
      intro bound typed object
      obtain ⟨rfl, objects⟩ := bag_objects object
      have members := members_of_bag (language := ambientCoreCalc) (block := ambientBlock) typed
      have moverTyped := members _ (List.getElem_mem hi)
      have moverObject := objects _ (List.getElem_mem hi)
      rw [mover] at moverTyped moverObject
      obtain ⟨nameTyped, innerBagTyped⟩ := amb_inv moverTyped
      obtain ⟨nameObject, innerBagObject⟩ := pair_objects moverObject
      obtain ⟨rfl, innerObjects⟩ := bag_objects innerBagObject
      have innerMembers := members_of_bag (language := ambientCoreCalc) (block := ambientBlock) innerBagTyped
      have capabilityTyped := innerMembers _ (List.getElem_mem hk)
      have capabilityObject := innerObjects _ (List.getElem_mem hk)
      rw [capability] at capabilityTyped capabilityObject
      obtain ⟨-, processTyped⟩ := prefix_inv (by simp) capabilityTyped
      obtain ⟨-, processObject⟩ := pair_objects capabilityObject
      have destinationTyped := members _ (List.mem_of_mem_eraseIdx (List.getElem_mem hj))
      have destinationObject := objects _ (List.mem_of_mem_eraseIdx (List.getElem_mem hj))
      rw [destination] at destinationTyped destinationObject
      obtain ⟨targetTyped, hostTyped⟩ := amb_inv destinationTyped
      obtain ⟨targetObject, hostObject⟩ := pair_objects destinationObject
      have movedTyped : HasType ambientCoreCalc free bound
          (.apply "AAmb" [name, .collection .hashBag (process :: inner.eraseIdx k) none]) procType :=
        amb_typed nameTyped (bag_typed_of fun element member => by
          simp only [List.mem_cons] at member
          rcases member with rfl | inRest
          · exact processTyped
          · exact innerMembers element (List.mem_of_mem_eraseIdx inRest))
      have movedObject : isObjectPattern
          (.apply "AAmb" [name, .collection .hashBag (process :: inner.eraseIdx k) none]) = true :=
        amb_object_of nameObject (bag_object_of fun element member => by
          simp only [List.mem_cons] at member
          rcases member with rfl | inRest
          · exact processObject
          · exact innerObjects element (List.mem_of_mem_eraseIdx inRest))
      have hostedTyped := amb_typed targetTyped (bag_typed_of (elements := [_, host]) fun element member => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl
        · exact movedTyped
        · exact hostTyped)
      have hostedObject := amb_object_of targetObject (bag_object_of (elements := [_, host]) fun element member => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl
        · exact movedObject
        · exact hostObject)
      refine ⟨bag_typed_of fun element member => ?_, bag_object_of fun element member => ?_⟩
      · simp only [List.mem_cons] at member
        rcases member with rfl | inRest
        · exact hostedTyped
        · exact members element (List.mem_of_mem_eraseIdx (List.mem_of_mem_eraseIdx inRest))
      · simp only [List.mem_cons] at member
        rcases member with rfl | inRest
        · exact hostedObject
        · exact objects element (List.mem_of_mem_eraseIdx (List.mem_of_mem_eraseIdx inRest))
  | @exit contents tail i hi name parent process inner innerTail k hk mover capability =>
      intro bound typed object
      obtain ⟨parentTyped, contentsTyped⟩ := amb_inv typed
      obtain ⟨parentObject, contentsObject⟩ := pair_objects object
      obtain ⟨rfl, objects⟩ := bag_objects contentsObject
      have members := members_of_bag (language := ambientCoreCalc) (block := ambientBlock) contentsTyped
      have moverTyped := members _ (List.getElem_mem hi)
      have moverObject := objects _ (List.getElem_mem hi)
      rw [mover] at moverTyped moverObject
      obtain ⟨nameTyped, innerBagTyped⟩ := amb_inv moverTyped
      obtain ⟨nameObject, innerBagObject⟩ := pair_objects moverObject
      obtain ⟨rfl, innerObjects⟩ := bag_objects innerBagObject
      have innerMembers := members_of_bag (language := ambientCoreCalc) (block := ambientBlock) innerBagTyped
      have capabilityTyped := innerMembers _ (List.getElem_mem hk)
      have capabilityObject := innerObjects _ (List.getElem_mem hk)
      rw [capability] at capabilityTyped capabilityObject
      obtain ⟨-, processTyped⟩ := prefix_inv (by simp) capabilityTyped
      obtain ⟨-, processObject⟩ := pair_objects capabilityObject
      have movedTyped : HasType ambientCoreCalc free bound
          (.apply "AAmb" [name, .collection .hashBag (process :: inner.eraseIdx k) none]) procType :=
        amb_typed nameTyped (bag_typed_of fun element member => by
          simp only [List.mem_cons] at member
          rcases member with rfl | inRest
          · exact processTyped
          · exact innerMembers element (List.mem_of_mem_eraseIdx inRest))
      have movedObject : isObjectPattern
          (.apply "AAmb" [name, .collection .hashBag (process :: inner.eraseIdx k) none]) = true :=
        amb_object_of nameObject (bag_object_of fun element member => by
          simp only [List.mem_cons] at member
          rcases member with rfl | inRest
          · exact processObject
          · exact innerObjects element (List.mem_of_mem_eraseIdx inRest))
      have leftTyped := amb_typed parentTyped (bag_typed_of (elements := contents.eraseIdx i) fun element member =>
        members element (List.mem_of_mem_eraseIdx member))
      have leftObject := amb_object_of parentObject (bag_object_of (elements := contents.eraseIdx i)
        fun element member => objects element (List.mem_of_mem_eraseIdx member))
      refine ⟨bag_typed_of fun element member => ?_, bag_object_of fun element member => ?_⟩
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl
        · exact movedTyped
        · exact leftTyped
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl
        · exact movedObject
        · exact leftObject
  | @par elements tail i hi target inner recurse =>
      intro bound typed object
      obtain ⟨rfl, objects⟩ := bag_objects object
      have members := members_of_bag (language := ambientCoreCalc) (block := ambientBlock) typed
      obtain ⟨steppedTyped, steppedObject⟩ :=
        recurse (members _ (List.getElem_mem hi)) (objects _ (List.getElem_mem hi))
      refine ⟨bag_typed_of fun element member => ?_, bag_object_of fun element member => ?_⟩
      · simp only [List.mem_cons] at member
        rcases member with rfl | inRest
        · exact steppedTyped
        · exact members element (List.mem_of_mem_eraseIdx inRest)
      · simp only [List.mem_cons] at member
        rcases member with rfl | inRest
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
      exact ⟨amb_typed nameTyped steppedTyped, amb_object_of nameObject steppedObject⟩

end Mettapedia.Languages.ProcessCalculi.Ambient.Steps
