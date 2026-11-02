import Mettapedia.OSLF.MeTTaIL.GeneralVectorCaptureTyping
import Mettapedia.OSLF.MeTTaIL.GeneralRuleBindingContextReading

/-! A grammar location in a constructor/vector schema points to a typed
subterm of every sorted ordinary instance. Bound contexts do not change in
this fragment; source declarations determine each selected argument type.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.GeneralFirstOrderProjection

open Syntax Match
open Mettapedia.GSLT.LanguageDef.WellSorted
open GeneralRuleBindingGrammar

theorem arguments_typed_at {language : LanguageDef} {free : FreeTypeContext} {bound : List TypeExpr}
    {arguments : List Pattern} {parameters : List TermParam} {index : Nat} {argument : Pattern}
    {parameter : TermParam} {expected : TypeExpr}
    (typed : ArgumentsHaveTypes language free bound arguments parameters)
    (argumentAt : arguments[index]? = some argument) (parameterAt : parameters[index]? = some parameter)
    (typeAt : parameterType? parameter = some expected) : HasType language free bound argument expected := by
  cases typed with
  | nil => cases argumentAt
  | cons _ declared head tail =>
      cases index with
      | zero =>
          cases Option.some.inj argumentAt
          cases Option.some.inj parameterAt
          have same := Option.some.inj (declared.symm.trans typeAt)
          exact same ▸ head
      | succ index => exact arguments_typed_at tail argumentAt parameterAt typeAt
termination_by index

theorem elements_typed_at {language : LanguageDef} {free : FreeTypeContext} {bound : List TypeExpr}
    {elements : List Pattern} {elementType : TypeExpr} {index : Nat} {element : Pattern}
    (typed : ElementsHaveType language free bound elements elementType)
    (selected : elements[index]? = some element) : HasType language free bound element elementType := by
  cases typed with
  | nil => cases selected
  | cons head tail =>
      cases index with
      | zero => cases Option.some.inj selected; exact head
      | succ index => exact elements_typed_at tail selected
termination_by index

theorem collection_origin_typed {language : LanguageDef} {free : FreeTypeContext} {bound : List TypeExpr}
    {kind : CollType} {elements : List Pattern} {type elementType : TypeExpr}
    (choices : CollectionChoiceDeterministic language)
    (origin : type = .collection kind elementType ∨ ∃ declaration ∈ language.terms,
      bareCollectionElementType? declaration kind type = some elementType)
    (typed : HasType language free bound (.collection kind elements none) type) :
    ElementsHaveType language free bound elements elementType := by
  rcases origin with direct | ⟨declaration, declared, selected⟩
  · subst type
    cases typed with
    | collection typed => exact typed
  · obtain ⟨typeSame, parameterName, shape⟩ :=
      (bareCollectionElementType?_eq_some_iff declaration kind type elementType).mp selected
    rcases hasType_collection_inversion typed with ⟨actualElement, impossible, _⟩ |
      ⟨actual, actualName, actualElement, actualMember, actualShape, actualType, targetElements⟩
    · rw [typeSame] at impossible
      cases impossible
    · have categories := TypeExpr.base.inj (typeSame.symm.trans actualType)
      have same := choices declared actualMember shape actualShape categories
      exact same ▸ targetElements

theorem vector_occurrence_instance_typed {language : LanguageDef} {free : FreeTypeContext}
    {context : List (String × TypeExpr)} {schema : Pattern} {path : List Nat} {type result : TypeExpr}
    {name : String} {assignment : Bindings}
    (labels : LabelDeterministic language) (choices : CollectionChoiceDeterministic language)
    (shape : VectorFirstOrder schema)
    (location : contextAt? language context [] type schema path = some ([], result))
    (variableAt : RuleBinding.occurrenceAt? schema path = some name)
    (sourceTyped : HasType language free [] (applyBindings assignment schema) type) :
    HasType language free [] (applyBindings assignment (.fvar name)) result := by
  induction path generalizing schema type with
  | nil =>
      cases shape with
      | metavariable actual =>
          have same : actual = name := Option.some.inj variableAt
          subst actual
          simp only [contextAt?] at location
          have typeSame := (Prod.mk.inj (Option.some.inj location)).2
          exact typeSame ▸ sourceTyped
      | constructor | vector => cases variableAt
  | cons index rest ih =>
      cases shape with
      | metavariable => cases variableAt
      | constructor label arguments children =>
          simp only [contextAt?, Option.bind_eq_bind, Option.bind_eq_some_iff] at location
          obtain ⟨declaration, selected, _, typeCheck, _, _, parameter, parameterAt, argument, argumentAt,
            _, _, argumentType, typeAt, nested⟩ := location
          obtain ⟨declared, named⟩ := constructor?_origin selected
          simp only [applyBindings] at sourceTyped
          obtain ⟨actual, actualMember, actualLabel, _, targetsTyped⟩ := application_typing sourceTyped
          have same := labels declared actualMember (named.trans actualLabel.symm)
          subst actual
          have actualAt : (arguments.map (applyBindings assignment))[index]? = some (applyBindings assignment argument) := by
            rw [List.getElem?_map, argumentAt]
            rfl
          apply ih (children argument (List.mem_of_getElem? argumentAt)) nested
            ?_ (arguments_typed_at targetsTyped actualAt parameterAt typeAt)
          simpa only [RuleBinding.occurrenceAt?, argumentAt, Option.bind_eq_bind, Option.bind_some] using variableAt
      | vector elements children =>
          simp only [contextAt?, Option.bind_eq_bind, Option.bind_eq_some_iff] at location
          obtain ⟨elementType, selected, remaining⟩ := location
          have origin := collectionElement?_origin selected
          split at remaining
          next inside =>
            obtain ⟨element, elementAt, nested⟩ := Option.bind_eq_some_iff.mp remaining
            have actualAt : (elements.map (applyBindings assignment))[index]? = some (applyBindings assignment element) := by
              rw [List.getElem?_map, elementAt]
              rfl
            simp only [applyBindings, List.append_nil] at sourceTyped
            have typed := collection_origin_typed choices origin sourceTyped
            apply ih (children element (List.mem_of_getElem? elementAt)) nested ?_ (elements_typed_at typed actualAt)
            simpa only [RuleBinding.occurrenceAt?, inside, if_true, elementAt, Option.bind_eq_bind, Option.bind_some] using variableAt
          next outside =>
            simp only [RuleBinding.occurrenceAt?, outside, if_false] at variableAt
            split at variableAt <;> cases variableAt

#print axioms vector_occurrence_instance_typed

end Mettapedia.OSLF.MeTTaIL.GeneralFirstOrderProjection
