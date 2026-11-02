import Mettapedia.Languages.ProcessCalculi.Ambient.DecodingRoot

/-!
# The padded form of an ambient process

Entering and leaving find a capability among the members of an ambient's content, so they fire where every ambient's
content is a bag. **The padded form** (`padA`) makes it one: a content that is no bag becomes the one member of a bag,
everywhere in the process. A process is equivalent to its padded form (`padA_equivalent`), since a one-member bag is
its member, so the padded form is a process of the same sort (`padA_typed`); it is an object term when the process
is (`padA_object`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.Ambient.Steps

open Mettapedia.Languages.ProcessCalculi.Ambient.Comm (ambientCoreCalc commTerms capRule)

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.GSLT.LanguageDef.BagNormalForm (elementsHaveType_iff isObjectPatternList_iff)
open Mettapedia.GSLT.LanguageDef.RestrictionBlocks (ProcEquiv Members SortedEquiv size restrict_fill
  collection_congr bag_body_equivalent)
open Mettapedia.Languages.ProcessCalculi.Ambient.Full (ambientBlock ambientRepBlock terms prefixRule
  amb_fill prefix_fill acap_fill input_fill)
open Mettapedia.Languages.ProcessCalculi.Ambient.Encoding (nameType procType name_cases_ambient)
open Mettapedia.Languages.ProcessCalculi.Ambient.Decoding (isMessage isVariable cap_isMessage)

/-- A process as a bag: a bag stays, anything else becomes the one member of a bag. -/
def asBag : Pattern → Pattern
  | .collection .hashBag elements none => .collection .hashBag elements none
  | process => .collection .hashBag [process] none

/-- An application with an ambient's content as a bag. -/
def padApply (label : String) : List Pattern → Pattern
  | [name, content] => if label = "AAmb" then .apply label [name, asBag content] else .apply label [name, content]
  | arguments => .apply label arguments

mutual
  /-- **The padded form**: every ambient's content a bag. -/
  def padA : Pattern → Pattern
    | .bvar index => .bvar index
    | .fvar name => .fvar name
    | .apply label arguments => padApply label (padAList arguments)
    | .lambda binder body => .lambda binder (padA body)
    | .multiLambda arity binders body => .multiLambda arity binders (padA body)
    | .subst body replacement => .subst (padA body) (padA replacement)
    | .collection kind elements rest => .collection kind (padAList elements) rest

  /-- The padded forms of the members of a list. -/
  def padAList : List Pattern → List Pattern
    | [] => []
    | pattern :: patterns => padA pattern :: padAList patterns
end

theorem padAList_eq_map : ∀ (patterns : List Pattern), padAList patterns = patterns.map padA
  | [] => by simp [padAList]
  | pattern :: patterns => by simp [padAList, padAList_eq_map patterns]

/-! ## Object terms -/

theorem asBag_object {process : Pattern} (object : isObjectPattern process = true) :
    isObjectPattern (asBag process) = true := by
  unfold asBag
  split
  · exact object
  · simpa [isObjectPattern, isObjectPatternList] using object

theorem padApply_object {label : String} {arguments : List Pattern}
    (objects : ∀ argument ∈ arguments, isObjectPattern argument = true) :
    isObjectPattern (padApply label arguments) = true := by
  unfold padApply
  split
  · rename_i name content
    have nameObject := objects name (by simp)
    have contentObject := objects content (by simp)
    split_ifs
    · simp [isObjectPattern, isObjectPatternList, nameObject, asBag_object contentObject]
    · simp [isObjectPattern, isObjectPatternList, nameObject, contentObject]
  · simpa [isObjectPattern, isObjectPatternList_iff] using objects

/-- **The padded form of an object term is an object term.** -/
theorem padA_object (pattern : Pattern) : isObjectPattern pattern = true → isObjectPattern (padA pattern) = true := by
  induction pattern using Pattern.inductionOn with
  | hbvar index => intro object; exact object
  | hfvar name => intro object; exact object
  | happly label arguments recurse =>
      intro object
      have objects : ∀ argument ∈ arguments, isObjectPattern argument = true := by
        simpa [isObjectPattern, isObjectPatternList_iff] using object
      simp only [padA, padAList_eq_map]
      exact padApply_object fun argument member => by
        obtain ⟨original, inArguments, rfl⟩ := List.mem_map.mp member
        exact recurse original inArguments (objects original inArguments)
  | hlambda binder body recurse =>
      intro object
      simp only [padA]
      simpa [isObjectPattern] using recurse (by simpa [isObjectPattern] using object)
  | hmultiLambda arity binders body recurse =>
      intro object
      simp only [padA]
      simpa [isObjectPattern] using recurse (by simpa [isObjectPattern] using object)
  | hsubst body replacement => intro object; simp [isObjectPattern] at object
  | hcollection kind elements rest recurse =>
      intro object
      simp only [padA, padAList_eq_map]
      simp only [isObjectPattern, Bool.and_eq_true, isObjectPatternList_iff] at object ⊢
      refine ⟨object.1, fun element member => ?_⟩
      obtain ⟨original, inElements, rfl⟩ := List.mem_map.mp member
      exact recurse original inElements (object.2 original inElements)

/-- **A message is its own padded form**: no ambient lies inside it. -/
theorem padA_message : ∀ {message : Pattern}, isMessage message = true → padA message = message
  | .bvar _, _ => rfl
  | .fvar _, _ => rfl
  | .apply _ [], _ => rfl
  | .apply label [name], isMsg => by
      simp only [isMessage, Bool.and_eq_true] at isMsg
      cases name <;> simp_all [isVariable, padA, padAList, padApply]
  | .apply label [first, second], isMsg => by
      simp only [isMessage, Bool.and_eq_true, beq_iff_eq] at isMsg
      obtain ⟨⟨rfl, firstMsg⟩, secondMsg⟩ := isMsg
      simp [padA, padAList, padApply, padA_message firstMsg, padA_message secondMsg]
  | .apply _ (_ :: _ :: _ :: _), isMsg => by simp [isMessage] at isMsg
  | .lambda _ _, isMsg => by simp [isMessage] at isMsg
  | .multiLambda _ _ _, isMsg => by simp [isMessage] at isMsg
  | .subst _ _, isMsg => by simp [isMessage] at isMsg
  | .collection _ _ _, isMsg => by simp [isMessage] at isMsg

/-! ## The padded form is equivalent -/

variable {free : FreeTypeContext}

/-- **A process is equivalent to itself as a bag**: a one-member bag is its member. -/
theorem asBag_equivalent {bound : List TypeExpr} {process : Pattern}
    (typed : HasType ambientCoreCalc free bound process procType) :
    ProcEquiv ambientCoreCalc ambientBlock free bound process (asBag process) := by
  have single : ProcEquiv ambientCoreCalc ambientBlock free bound process
      (.collection .hashBag [process] none) :=
    .symm _ _ (bag_body_equivalent (language := ambientCoreCalc) (block := ambientBlock) fun element member => by
      simp only [List.mem_singleton] at member
      subst member
      exact typed)
  unfold asBag
  split
  · exact .refl _
  · exact single

/-- **A process is equivalent to its padded form.** -/
theorem padA_equivalent : ∀ (fuel : Nat) {bound : List TypeExpr} {process : Pattern}, size process < fuel →
    HasType ambientCoreCalc free bound process procType → isObjectPattern process = true →
    ProcEquiv ambientCoreCalc ambientBlock free bound process (padA process)
  | 0, _, _, small, _, _ => absurd small (Nat.not_lt_zero _)
  | fuel + 1, bound, process, small, typed, object => by
      cases process with
      | bvar index => exact .refl _
      | fvar name => exact .refl _
      | lambda binder body => cases typed
      | multiLambda arity binders body => cases typed
      | subst body replacement => simp [isObjectPattern] at object
      | collection kind elements rest =>
          rcases hasType_collection_inversion typed with ⟨_, typeIs, _⟩ |
            ⟨rule, parameterName, elementType, member, shape, typeIs, elementsTyped⟩
          · cases typeIs
          · simp only [ambientCoreCalc, terms, commTerms, prefixRule, capRule, List.cons_append,
   List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at member
            rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
              rfl | rfl | rfl <;>
              simp [GrammarRule.bareParams] at shape
            obtain ⟨rfl, rfl, rfl⟩ := shape
            have tailNone : rest = none := by
              simpa [isObjectPattern] using (Bool.and_eq_true _ _).mp object |>.1
            subst tailNone
            have objects : ∀ element ∈ elements, isObjectPattern element = true := by
              simpa [isObjectPattern, isObjectPatternList_iff] using object
            have members : Members ambientCoreCalc ambientBlock free bound elements :=
              fun element member => elementsHaveType_iff.mp elementsTyped element member
            have related : List.Forall₂ (ProcEquiv ambientCoreCalc ambientBlock free bound) elements
                (elements.map padA) := by
              rw [List.forall₂_map_right_iff]
              refine List.forall₂_same.mpr fun element member => ?_
              have elementSmall : size element < fuel := by
                have := Mettapedia.GSLT.LanguageDef.RestrictionBlocks.size_lt_of_mem member
                simp only [size] at small
                omega
              exact padA_equivalent fuel elementSmall (members element member) (objects element member)
            simp only [padA, padAList_eq_map]
            exact collection_congr (language := ambientCoreCalc) (block := ambientBlock) none members related []
              Members.nil
      | apply label arguments =>
          obtain ⟨rule, member, rfl, notBare, typeIs, argumentsTyped⟩ := hasType_apply_inversion typed
          have objects : ∀ argument ∈ arguments, isObjectPattern argument = true := by
            simpa [isObjectPattern, isObjectPatternList_iff] using object
          have argumentSmall : ∀ argument ∈ arguments, size argument < fuel := by
            intro argument inArguments
            have := Mettapedia.GSLT.LanguageDef.RestrictionBlocks.size_lt_of_mem inArguments
            simp only [size] at small
            omega
          simp only [ambientCoreCalc, terms, commTerms, prefixRule, capRule, List.cons_append,
            List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at member
          rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
            rfl | rfl | rfl <;>
            simp only [procType, TypeExpr.base.injEq] at typeIs <;> try (exact absurd typeIs (by decide))
          · -- inaction
            cases argumentsTyped
            exact .refl _
          · exact absurd ⟨"ps", .hashBag, .base "Proc", rfl⟩ notBare
          · -- restriction
            cases argumentsTyped with
            | cons representation parameterType argumentTyped rest =>
                cases rest
                obtain ⟨body, rfl⟩ :=
                  (matchesParameterRepresentation_abstractionNamed_iff _ _ _ _).mp representation
                simp only [parameterType?, Option.some.injEq] at parameterType
                subst parameterType
                cases argumentTyped with
                | lambda bodyTyped =>
                    have bodySmall : size body < fuel := by
                      have := argumentSmall _ List.mem_cons_self
                      simp only [size] at this
                      omega
                    have bodyObject : isObjectPattern body = true := by
                      simpa [isObjectPattern] using objects _ List.mem_cons_self
                    exact restrict_fill (language := ambientCoreCalc) (block := ambientBlock)
                      (padA_equivalent fuel bodySmall bodyTyped bodyObject)
          · -- replication
            cases argumentsTyped with
            | @cons _ argument _ _ _ _ representation parameterType argumentTyped rest =>
                cases rest
                simp only [parameterType?, Option.some.injEq] at parameterType
                subst parameterType
                exact Mettapedia.GSLT.LanguageDef.RestrictionBlocks.replicate_fill (language := ambientCoreCalc)
                  (block := ambientRepBlock)
                  (padA_equivalent fuel (argumentSmall _ List.mem_cons_self) argumentTyped (objects _ List.mem_cons_self))
          · -- an ambient
            cases argumentsTyped with
            | @cons _ name _ _ _ _ nameRepresentation nameParameter nameTyped rest =>
                cases rest with
                | @cons _ content _ _ _ _ contentRepresentation contentParameter contentTyped last =>
                    cases last
                    simp only [parameterType?, Option.some.injEq] at nameParameter contentParameter
                    subst nameParameter contentParameter
                    have contentSmall : size content < fuel :=
                      argumentSmall _ (List.mem_cons_of_mem _ List.mem_cons_self)
                    have contentObject : isObjectPattern content = true :=
                      objects _ (List.mem_cons_of_mem _ List.mem_cons_self)
                    have padded := padA_equivalent fuel contentSmall contentTyped contentObject
                    have paddedTyped := (SortedEquiv.typed_iff padded).mp contentTyped
                    have nameSame : padA name = name := by
                      rcases name_cases_ambient nameTyped rfl (objects _ List.mem_cons_self) with
                        ⟨_, rfl, _⟩ | ⟨_, rfl, _⟩ <;> rfl
                    show ProcEquiv ambientCoreCalc ambientBlock free bound (.apply "AAmb" [name, content])
                      (padApply "AAmb" (padAList [name, content]))
                    simp only [padAList, padApply, if_true, nameSame]
                    exact amb_fill nameTyped (.trans _ _ _ padded (asBag_equivalent paddedTyped))
          rotate_left 3
          · -- a prefix by a capability term: its message as it is, its continuation padded
            cases argumentsTyped with
            | @cons _ capability _ _ _ _ capRepresentation capParameter capabilityTyped rest =>
                cases rest with
                | @cons _ content _ _ _ _ contentRepresentation contentParameter contentTyped last =>
                    cases last
                    simp only [parameterType?, Option.some.injEq] at capParameter contentParameter
                    subst capParameter contentParameter
                    have padded := padA_equivalent fuel (argumentSmall _ (List.mem_cons_of_mem _ List.mem_cons_self))
                      contentTyped (objects _ (List.mem_cons_of_mem _ List.mem_cons_self))
                    have capabilitySame : padA capability = capability :=
                      padA_message (cap_isMessage capabilityTyped (objects _ List.mem_cons_self))
                    simp only [padA, padAList, padApply, capabilitySame, show ¬ ("ACap" = "AAmb") by decide,
                      if_false]
                    exact acap_fill capabilityTyped padded
          all_goals try (
            cases argumentsTyped with
            | cons representation parameterType argumentTyped rest =>
                cases rest
                obtain ⟨body, rfl⟩ :=
                  (matchesParameterRepresentation_abstractionNamed_iff _ _ _ _).mp representation
                simp only [parameterType?, Option.some.injEq] at parameterType
                subst parameterType
                cases argumentTyped with
                | lambda bodyTyped =>
                    have bodySmall : size body < fuel := by
                      have := argumentSmall _ List.mem_cons_self
                      simp only [size] at this
                      omega
                    have bodyObject : isObjectPattern body = true := by
                      simpa [isObjectPattern] using objects _ List.mem_cons_self
                    simp only [padA, padAList, padApply]
                    first
                      | exact input_fill (sort := "Name") (by simp) (padA_equivalent fuel bodySmall bodyTyped bodyObject)
                      | exact input_fill (sort := "Cap") (by simp) (padA_equivalent fuel bodySmall bodyTyped bodyObject))
          -- outputs: their messages as they are
          all_goals try (
            cases argumentsTyped with
            | @cons _ message _ _ _ _ representation parameterType messageTyped rest =>
                cases rest
                simp only [parameterType?, Option.some.injEq] at parameterType
                subst parameterType
                have messageSame : padA message = message := by
                  first
                    | exact padA_message (cap_isMessage messageTyped (objects _ List.mem_cons_self))
                    | rcases name_cases_ambient messageTyped rfl (objects _ List.mem_cons_self) with
                        ⟨_, rfl, _⟩ | ⟨_, rfl, _⟩ <;> rfl
                simp only [padA, padAList, padApply, messageSame]
                exact .refl _)
          all_goals
            cases argumentsTyped with
            | @cons _ name _ _ _ _ nameRepresentation nameParameter nameTyped rest =>
                cases rest with
                | @cons _ content _ _ _ _ contentRepresentation contentParameter contentTyped last =>
                    cases last
                    simp only [parameterType?, Option.some.injEq] at nameParameter contentParameter
                    subst nameParameter contentParameter
                    have padded := padA_equivalent fuel (argumentSmall _ (List.mem_cons_of_mem _ List.mem_cons_self))
                      contentTyped (objects _ (List.mem_cons_of_mem _ List.mem_cons_self))
                    have nameSame : padA name = name := by
                      rcases name_cases_ambient nameTyped rfl (objects _ List.mem_cons_self) with
                        ⟨_, rfl, _⟩ | ⟨_, rfl, _⟩ <;> rfl
                    simp only [padA, padAList, padApply, nameSame]
                    simp only [show ¬ ("AIn" = "AAmb") by decide, show ¬ ("AOut" = "AAmb") by decide,
                      show ¬ ("AOpen" = "AAmb") by decide, if_false]
                    exact prefix_fill (by simp) nameTyped padded

/-- **The padded form of a process is a process.** -/
theorem padA_typed {bound : List TypeExpr} {process : Pattern}
    (typed : HasType ambientCoreCalc free bound process procType) (object : isObjectPattern process = true) :
    HasType ambientCoreCalc free bound (padA process) procType :=
  (SortedEquiv.typed_iff (padA_equivalent (size process + 1) (Nat.lt_succ_self _) typed object)).mp typed

end Mettapedia.Languages.ProcessCalculi.Ambient.Steps
