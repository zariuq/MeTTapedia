import Mettapedia.OSLF.MeTTaIL.GeneralGrammarLookupCompletion
import Mettapedia.OSLF.MeTTaIL.GeneralVectorAddressMetadata

/-! Grammar inspection is complete on sorted constructor/vector schemas
with unique constructor labels and uniquely determined collection carriers.
Each inferred result is the source free-context assignment at that name.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.GeneralFirstOrderProjection

open Syntax RuleBinding GeneralRuleBindingGrammar
open Mettapedia.GSLT.LanguageDef.WellSorted

theorem typed_argument_origin {language : LanguageDef} {free : FreeTypeContext}
    {bound : List TypeExpr} {arguments : List Pattern} {parameters : List TermParam}
    (typed : ArgumentsHaveTypes language free bound arguments parameters)
    (index : Nat) (argument : Pattern) (selected : arguments[index]? = some argument) :
    ∃ parameter expected, parameters[index]? = some parameter ∧ parameterType? parameter = some expected ∧
      MatchesParameterRepresentation parameter argument ∧ HasType language free bound argument expected := by
  cases typed with
  | nil => cases selected
  | cons representation typeRead head tail =>
      cases index with
      | zero =>
          cases Option.some.inj selected
          exact ⟨_, _, rfl, typeRead, representation, head⟩
      | succ index => exact typed_argument_origin tail index argument selected
termination_by index

theorem vector_context_complete {language : LanguageDef} {free : FreeTypeContext} {schema : Pattern}
    {expected : TypeExpr} (labels : (language.terms.map GrammarRule.label).Nodup)
    (choices : CollectionChoiceDeterministic language) (shape : VectorFirstOrder schema)
    (typed : HasType language free [] schema expected) (path : List Nat) (name : String)
    (found : occurrenceAt? schema path = some name) :
    ∃ result, contextAt? language [] [] expected schema path = some ([], result) ∧ free name = some result := by
  induction path generalizing schema expected with
  | nil =>
      cases shape with
      | metavariable actual =>
          cases Option.some.inj found
          cases typed with
          | fvar assigned => exact ⟨_, by simp only [contextAt?], assigned⟩
      | constructor | vector => cases found
  | cons index rest ih =>
      cases shape with
      | metavariable => cases found
      | constructor label arguments children =>
          obtain ⟨child, childAt, remaining⟩ := Option.bind_eq_some_iff.mp found
          cases typed with
          | @constructor _ declaration _ declared notBare argumentsTyped =>
              obtain ⟨parameter, argumentType, parameterAt, typeAt, representation, childTyped⟩ :=
                typed_argument_origin argumentsTyped index child childAt
              obtain ⟨result, located, assigned⟩ := ih (children child (List.mem_of_getElem? childAt)) childTyped remaining
              have ordinary : usesBareCollection? declaration = false := by
                apply Bool.eq_false_iff.mpr
                intro present
                exact notBare ((usesBareCollection?_eq_true_iff _).mp present)
              refine ⟨result, ?_, assigned⟩
              simp only [contextAt?, constructor?_complete language declaration labels declared,
                beq_self_eq_true, ordinary, Bool.not_false, guard, if_true, Option.pure_def,
                Option.bind_eq_bind, Option.bind_some, parameterAt, childAt, typeAt,
                (matchesParameterRepresentation?_eq_true_iff _ _).mpr representation, located]
      | vector elements children =>
          simp only [occurrenceAt?] at found
          split at found
          next inside =>
            obtain ⟨child, childAt, remaining⟩ := Option.bind_eq_some_iff.mp found
            have elementsTyped : ∃ elementType,
                (expected = .collection .vec elementType ∨ ∃ declaration ∈ language.terms,
                  bareCollectionElementType? declaration .vec expected = some elementType) ∧
                ElementsHaveType language free [] elements elementType := by
              rcases hasType_collection_inversion typed with ⟨elementType, same, values⟩ |
                ⟨declaration, parameterName, elementType, declared, parameterShape, same, values⟩
              · exact ⟨elementType, Or.inl same, values⟩
              · exact ⟨elementType, Or.inr ⟨declaration, declared,
                  (bareCollectionElementType?_eq_some_iff _ _ _ _).mpr ⟨same, parameterName, parameterShape⟩⟩, values⟩
            obtain ⟨elementType, origin, values⟩ := elementsTyped
            obtain ⟨result, located, assigned⟩ := ih (children child (List.mem_of_getElem? childAt))
              (elements_typed_at values childAt) remaining
            refine ⟨result, ?_, assigned⟩
            simp only [contextAt?, collectionElement?_complete language choices .vec expected elementType origin,
              Option.bind_eq_bind, Option.bind_some, inside, if_true, childAt, located]
          next outside => split at found <;> cases found

theorem inspect_vector_complete {language : LanguageDef} {free : FreeTypeContext} {schema : Pattern}
    {expected : TypeExpr} (labels : (language.terms.map GrammarRule.label).Nodup)
    (choices : CollectionChoiceDeterministic language) (shape : VectorFirstOrder schema)
    (typed : HasType language free [] schema expected) (site : RulePatternSite) :
    ∃ rows, inspect language [] site [] expected schema = some rows ∧
      ∀ row ∈ rows, free row.name = some row.result := by
  have each : ∀ address ∈ addresses site [] schema, ∃ row,
      (do
        let (localBound, result) ← contextAt? language [] [] expected schema address.path
        pure (Occurrence.mk address localBound result)) = some row := by
    intro address member
    obtain ⟨suffix, same, found⟩ := vector_address_sound shape site [] address member
    have actual : occurrenceAt? schema address.path = some address.name := by
      simpa only [List.nil_append] using (same ▸ found)
    obtain ⟨result, located, _⟩ := vector_context_complete labels choices shape typed address.path address.name actual
    exact ⟨⟨address, [], result⟩, by simp [located]⟩
  obtain ⟨rows, inspected⟩ := Mettapedia.Data.List.option_mapM_exists _ (addresses site [] schema) each
  refine ⟨rows, inspected, ?_⟩
  intro row member
  have origin := inspect_origin language [] site [] expected schema rows inspected row member
  obtain ⟨suffix, same, found⟩ := vector_address_sound shape site [] row.toAddress origin.1
  have actual : occurrenceAt? schema row.path = some row.name := by
    simpa only [List.nil_append] using (same ▸ found)
  obtain ⟨result, located, assigned⟩ := vector_context_complete labels choices shape typed row.path row.name actual
  have pairSame := Option.some.inj (located.symm.trans origin.2)
  exact (congrArg some (congrArg Prod.snd pairSame)) ▸ assigned

#print axioms typed_argument_origin
#print axioms vector_context_complete
#print axioms inspect_vector_complete

end Mettapedia.OSLF.MeTTaIL.GeneralFirstOrderProjection
