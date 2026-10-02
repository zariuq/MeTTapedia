import Mettapedia.GSLT.LanguageDef.ReflectiveNormalizationTyping
import Mettapedia.GSLT.LanguageDef.Continued.ContinuationDecorationBinding

/-!
# Sorted binder-eliminating reflection

Typing comes from the authored language and the existing quote/drop validation
witness. Sealing and the operational name-form check remain explicit source
premises. No preservation of literal-quote admission is inferred for an open
received payload.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ReflectiveInstantiationTyping

open WellSorted ReflectiveNormalizationTyping
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Substitution
open Mettapedia.OSLF.MeTTaIL.ScopedPattern
open Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution
open Mettapedia.OSLF.MeTTaIL.ReflectiveInstantiation

variable {language : LanguageDef} {declaration : ReflectivePresentationDecl}

theorem unary_constructor_hasType
    {free : FreeTypeContext} {bound : List TypeExpr}
    {constructor : String} {rule : GrammarRule} {parameter : String}
    {argument : TypeExpr} {payload : Pattern}
    (unique : language.terms.filter (fun candidate => candidate.label == constructor) = [rule])
    (parameters : rule.params = [.simple parameter argument])
    (notCollection : ∀ kind element, argument ≠ .collection kind element)
    (typed : HasType language free bound payload argument) :
    HasSort language free bound (.apply constructor [payload]) rule.category := by
  have selected : rule ∈ language.terms.filter (fun candidate => candidate.label == constructor) := by
    rw [unique]
    exact List.mem_singleton_self _
  obtain ⟨member, label⟩ := List.mem_filter.mp selected
  have labelEq : rule.label = constructor := beq_iff_eq.mp label
  rw [← labelEq]
  apply HasType.constructor member
  · rintro ⟨name, kind, element, shape⟩
    rw [parameters] at shape
    have equality : argument = .collection kind element := by
      have sameTypes := congrArg (List.map TermParam.typeExpr) shape
      simpa [TermParam.typeExpr] using sameTypes
    exact notCollection kind element equality
  · rw [parameters]
    exact .cons trivial rfl typed .nil

theorem drop_hasType (witness : LanguageDef.ReflectivePresentationWitness language declaration)
    {free : FreeTypeContext} {bound : List TypeExpr} {name : Pattern}
    (typed : HasSort language free bound name declaration.nameSort) :
    HasSort language free bound (.apply declaration.dropConstructor [name]) declaration.processSort := by
  have result := unary_constructor_hasType witness.dropUnique witness.dropParameters
    (by intros; simp) typed
  simpa only [witness.dropCategory] using result

theorem quote_hasType (witness : LanguageDef.ReflectivePresentationWitness language declaration)
    {free : FreeTypeContext} {bound : List TypeExpr} {process : Pattern}
    (typed : HasSort language free bound process declaration.processSort) :
    HasSort language free bound (.apply declaration.quoteConstructor [process]) declaration.nameSort := by
  have result := unary_constructor_hasType witness.quoteUnique witness.quoteParameters
    (by intros; simp) typed
  simpa only [witness.quoteCategory] using result

/-- Remove the communication binder from an opaque term known to be closed
to all surrounding bound variables, using the existing typed substitution. -/
theorem closed_remove_binder
    {free : FreeTypeContext} {bound binders : List TypeExpr}
    {pattern replacement : Pattern} {domain result : TypeExpr}
    (typed : HasType language free (binders ++ domain :: bound) pattern result)
    (closed : pattern.isWellScopedAt 0 = true)
    (replacementTyped : HasType language free bound replacement domain) :
    HasType language free (binders ++ bound) pattern result := by
  have resultTyped := typed.instantiateBVarAt replacementTyped
  rwa [instantiateBVarAt_eq_self_of_isWellScopedAt
    (isWellScopedAt_mono closed (Nat.zero_le binders.length))] at resultTyped

theorem atomicOrClosed_of_closed {pattern : Pattern}
    (closed : pattern.isWellScopedAt 0 = true) :
    atomicOrClosed declaration pattern = true := by
  have normalized := normalizeReflective_scoped declaration closed
  unfold atomicOrClosed
  generalize normalizeReflective declaration pattern = result at normalized ⊢
  cases result <;> first | rfl | exact normalized

/-- Atomic name comparison preserves the declared name sort. Compound names
are accepted here only when their normalized form has no ambient dependency. -/
theorem nameMark_hasType
    (witness : LanguageDef.ReflectivePresentationWitness language declaration)
    {free : FreeTypeContext} {bound binders : List TypeExpr} {name replacement : Pattern}
    (typed : HasSort language free (binders ++ .base declaration.nameSort :: bound)
      name declaration.nameSort)
    (admitted : atomicOrClosed declaration name = true)
    (replacementTyped : HasSort language free bound replacement declaration.nameSort) :
    HasSort language free (binders ++ bound)
      (nameMark declaration binders.length replacement name).1 declaration.nameSort := by
  have normalizedTyped := normalizeReflective_hasType witness typed
  unfold nameMark atomicOrClosed at *
  generalize normalizeReflective declaration name = normalized at normalizedTyped admitted ⊢
  cases normalized with
  | bvar index => exact normalizedTyped.instantiateBVarAt replacementTyped
  | fvar name => exact closed_remove_binder normalizedTyped admitted replacementTyped
  | apply constructor arguments => exact closed_remove_binder normalizedTyped admitted replacementTyped
  | lambda binder body => exact closed_remove_binder normalizedTyped admitted replacementTyped
  | multiLambda arity names body => exact closed_remove_binder normalizedTyped admitted replacementTyped
  | subst body value => exact closed_remove_binder normalizedTyped admitted replacementTyped
  | collection kind elements rest => exact closed_remove_binder normalizedTyped admitted replacementTyped

private theorem instantiation_representation (declaration : ReflectivePresentationDecl)
    (depth : Nat) (replacement : Pattern) (parameter : TermParam) (pattern : Pattern)
    (represented : MatchesParameterRepresentation parameter pattern) :
    MatchesParameterRepresentation parameter (instantiate declaration depth replacement pattern) := by
  cases parameter with
  | simple => trivial
  | abstractionNamed binder name type =>
      obtain ⟨body, rfl⟩ :=
        (matchesParameterRepresentation_abstractionNamed_iff binder name type pattern).mp represented
      trivial
  | multiAbstractionNamed binders name type =>
      obtain ⟨arity, body, rfl⟩ :=
        (matchesParameterRepresentation_multiAbstractionNamed_iff binders name type pattern).mp represented
      trivial

mutual
  /-- Eliminate a received name below an arbitrary heterogeneous binder prefix
  while retaining the type derived from the exact authored constructor rows. -/
  theorem instantiate_hasType
      (witness : LanguageDef.ReflectivePresentationWitness language declaration)
      {free : FreeTypeContext} {bound binders : List TypeExpr}
      {body replacement : Pattern} {result : TypeExpr}
      (typed : HasType language free (binders ++ .base declaration.nameSort :: bound) body result)
      (sealed : binderSafeAt declaration.quoteConstructor
        (binders ++ .base declaration.nameSort :: bound).length body = true)
      (names : namesAdmitted declaration body = true)
      (replacementTyped : HasSort language free bound replacement declaration.nameSort) :
      HasType language free (binders ++ bound)
        (instantiate declaration binders.length replacement body) result := by
    cases typed with
    | bvar lookup => exact (HasType.bvar lookup).instantiateBVarAt replacementTyped
    | fvar lookup => exact .fvar lookup
    | @constructor _ rule arguments membership notBare argumentsTyped =>
        have sourceTyped := HasType.constructor membership notBare argumentsTyped
        cases arguments with
        | nil =>
            have parametersEmpty : rule.params = [] :=
              List.eq_nil_iff_length_eq_zero.mpr argumentsTyped.length_eq.symm
            exact .constructor membership notBare (by rw [parametersEmpty]; exact .nil)
        | cons first rest =>
            cases rest with
            | nil =>
                by_cases quoted : rule.label = declaration.quoteConstructor
                · have quoteTyped : HasType language free
                      (binders ++ .base declaration.nameSort :: bound)
                      (.apply declaration.quoteConstructor [first]) (.base rule.category) := by
                    simpa only [quoted] using sourceTyped
                  have resultEq := (quote_inv witness quoteTyped).1
                  have firstClosed : first.isWellScopedAt 0 = true :=
                    isWellScopedAt_of_binderSafeAt _
                      (by simpa [binderSafeAt, quoted] using sealed)
                  have wholeClosed : (Pattern.apply declaration.quoteConstructor [first]).isWellScopedAt 0 = true := by
                    simpa [Pattern.isWellScopedAt, Pattern.isWellScopedListAt] using firstClosed
                  simp only [instantiate, quoted, beq_self_eq_true, if_true]
                  rw [resultEq]
                  exact nameMark_hasType witness (by simpa only [resultEq] using quoteTyped)
                    (atomicOrClosed_of_closed wholeClosed) replacementTyped
                · have firstSealed : binderSafeAt declaration.quoteConstructor
                      (binders ++ .base declaration.nameSort :: bound).length first = true := by
                    simpa [binderSafeAt, quoted, binderSafeListAt] using sealed
                  by_cases dropped : rule.label = declaration.dropConstructor
                  · have dropTyped : HasType language free
                        (binders ++ .base declaration.nameSort :: bound)
                        (.apply declaration.dropConstructor [first]) (.base rule.category) := by
                      simpa only [dropped] using sourceTyped
                    obtain ⟨resultEq, nameTyped⟩ := drop_inv witness dropTyped
                    have admitted : atomicOrClosed declaration first = true := by
                      simpa only [namesAdmitted, beq_iff_eq, if_neg quoted, if_pos dropped] using names
                    have markedTyped := nameMark_hasType witness nameTyped admitted replacementTyped
                    simp only [instantiate, beq_iff_eq, if_neg quoted, if_pos dropped]
                    rw [resultEq]
                    generalize markedEq : nameMark declaration binders.length replacement first = marked at markedTyped ⊢
                    rcases marked with ⟨name, matched⟩
                    simp only at markedTyped ⊢
                    split
                    · rename_i quote process
                      split
                      · rename_i quoteEq
                        subst quote
                        exact (quote_inv witness markedTyped).2
                      · simpa only [dropped] using drop_hasType witness markedTyped
                    · simpa only [dropped] using drop_hasType witness markedTyped
                  · have argumentSealed : binderSafeListAt declaration.quoteConstructor
                        (binders ++ .base declaration.nameSort :: bound).length [first] = true := by
                      simpa [binderSafeListAt] using firstSealed
                    have argumentNames : namesAdmittedList declaration [first] = true := by
                      simpa only [namesAdmitted, beq_iff_eq, if_neg quoted, if_neg dropped,
                        namesAdmittedList, Bool.and_true] using names
                    have args := instantiate_arguments_hasType witness argumentsTyped argumentSealed argumentNames replacementTyped
                    simpa [instantiate, quoted, dropped, instantiateList] using
                      HasType.constructor membership notBare args
            | cons second more =>
                exact .constructor membership notBare
                  (instantiate_arguments_hasType witness argumentsTyped sealed names replacementTyped)
    | @lambda _ binder body domain codomain bodyTyped =>
        have transformed := instantiate_hasType witness (binders := domain :: binders)
          bodyTyped (by simpa [binderSafeAt] using sealed) names replacementTyped
        simpa [instantiate, List.length_cons, Nat.add_comm] using HasType.lambda transformed
    | @multiLambda _ arity binderNames body domain codomain bodyTyped =>
        have bodyTyped' : HasType language free
            ((List.replicate arity domain ++ binders) ++ .base declaration.nameSort :: bound) body codomain := by
          simpa [List.append_assoc] using bodyTyped
        have transformed := instantiate_hasType witness bodyTyped'
          (by simpa [binderSafeAt, List.length_append, List.length_replicate,
            Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using sealed) names replacementTyped
        have transformed' : HasType language free
            (List.replicate arity domain ++ (binders ++ bound))
            (instantiate declaration (binders.length + arity) replacement body) codomain := by
          simpa [List.append_assoc, List.length_append, List.length_replicate, Nat.add_comm] using transformed
        exact HasType.multiLambda (binders := binderNames) transformed'
    | @subst _ body value domain codomain bodyTyped valueTyped =>
        simp only [binderSafeAt, Bool.and_eq_true] at sealed
        simp only [namesAdmitted, Bool.and_eq_true] at names
        have transformedBody := instantiate_hasType witness (binders := domain :: binders)
          bodyTyped (by simpa using sealed.1) names.1 replacementTyped
        have transformedValue := instantiate_hasType witness valueTyped sealed.2 names.2 replacementTyped
        simpa [instantiate, List.length_cons, Nat.add_comm] using HasType.subst transformedBody transformedValue
    | collection elementsTyped =>
        exact .collection (instantiate_elements_hasType witness elementsTyped sealed names replacementTyped)
    | collectionConstructor membership parameters elementsTyped =>
        exact .collectionConstructor membership parameters
          (instantiate_elements_hasType witness elementsTyped sealed names replacementTyped)

  theorem instantiate_arguments_hasType
      (witness : LanguageDef.ReflectivePresentationWitness language declaration)
      {free : FreeTypeContext} {bound binders : List TypeExpr}
      {patterns : List Pattern} {parameters : List TermParam} {replacement : Pattern}
      (typed : ArgumentsHaveTypes language free (binders ++ .base declaration.nameSort :: bound)
        patterns parameters)
      (sealed : binderSafeListAt declaration.quoteConstructor
        (binders ++ .base declaration.nameSort :: bound).length patterns = true)
      (names : namesAdmittedList declaration patterns = true)
      (replacementTyped : HasSort language free bound replacement declaration.nameSort) :
      ArgumentsHaveTypes language free (binders ++ bound)
        (instantiateList declaration binders.length replacement patterns) parameters := by
    cases typed with
    | nil => exact .nil
    | cons represented expected headTyped tailTyped =>
        simp only [binderSafeListAt, Bool.and_eq_true] at sealed
        simp only [namesAdmittedList, Bool.and_eq_true] at names
        exact .cons (instantiation_representation _ _ _ _ _ represented) expected
          (instantiate_hasType witness headTyped sealed.1 names.1 replacementTyped)
          (instantiate_arguments_hasType witness tailTyped sealed.2 names.2 replacementTyped)

  theorem instantiate_elements_hasType
      (witness : LanguageDef.ReflectivePresentationWitness language declaration)
      {free : FreeTypeContext} {bound binders : List TypeExpr}
      {patterns : List Pattern} {type : TypeExpr} {replacement : Pattern}
      (typed : ElementsHaveType language free (binders ++ .base declaration.nameSort :: bound) patterns type)
      (sealed : binderSafeListAt declaration.quoteConstructor
        (binders ++ .base declaration.nameSort :: bound).length patterns = true)
      (names : namesAdmittedList declaration patterns = true)
      (replacementTyped : HasSort language free bound replacement declaration.nameSort) :
      ElementsHaveType language free (binders ++ bound)
        (instantiateList declaration binders.length replacement patterns) type := by
    cases typed with
    | nil => exact .nil _ _
    | cons headTyped tailTyped =>
        simp only [binderSafeListAt, Bool.and_eq_true] at sealed
        simp only [namesAdmittedList, Bool.and_eq_true] at names
        exact .cons (instantiate_hasType witness headTyped sealed.1 names.1 replacementTyped)
          (instantiate_elements_hasType witness tailTyped sealed.2 names.2 replacementTyped)
end

#print axioms instantiate_hasType

end Mettapedia.GSLT.LanguageDef.ReflectiveInstantiationTyping
