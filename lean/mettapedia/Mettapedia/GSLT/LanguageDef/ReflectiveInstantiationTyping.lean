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
open Mettapedia.OSLF.MeTTaIL.ReflectiveCoherent

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
    have shape := (GrammarRule.bareParams_cons_iff _ _ _).mp shape |>.2
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

theorem receive_hasType (witness : LanguageDef.ReflectivePresentationWitness language declaration)
    {free : FreeTypeContext} {bound : List TypeExpr} {name : Pattern}
    (typed : HasSort language free bound name declaration.nameSort) :
    HasSort language free bound (receive declaration declaration.dropConstructor name)
      declaration.processSort := by
  rcases receive_cases (declaration := declaration) declaration.dropConstructor name with
    plain | ⟨process, rfl, ran⟩
  · rw [plain]; exact drop_hasType witness typed
  · rw [ran]; exact (quote_inv witness typed).2

private theorem elementsHaveType_mem {free : FreeTypeContext} {bound : List TypeExpr}
    {elements : List Pattern} {type : TypeExpr}
    (typed : ElementsHaveType language free bound elements type) {element : Pattern}
    (membership : element ∈ elements) : HasType language free bound element type := by
  induction elements with
  | nil => simp at membership
  | cons head tail ih =>
      cases typed with
      | cons headTyped tailTyped =>
          rcases List.mem_cons.mp membership with rfl | membership
          · exact headTyped
          · exact ih tailTyped membership

/-- Every member of a typed parallel composition is typed. -/
theorem parallelLeaves_typed {free : FreeTypeContext} {bound : List TypeExpr}
    {pattern member : Pattern} {type : TypeExpr}
    (typed : HasType language free bound pattern type)
    (membership : member ∈ parallelLeaves declaration pattern) :
    ∃ memberType, HasType language free bound member memberType := by
  induction pattern using Pattern.inductionOn generalizing type with
  | hcollection kind elements rest ih =>
      have single : member = .collection kind elements rest → ∃ memberType,
          HasType language free bound member memberType := fun same => ⟨type, same ▸ typed⟩
      cases rest with
      | some rest =>
          simp only [parallelLeaves, List.mem_singleton] at membership; exact single membership
      | none =>
          by_cases parallel : kind = declaration.parallelCollection
          · simp only [parallelLeaves, parallel, if_true, parallelLeavesList_eq_flatMap,
              List.mem_flatMap] at membership
            obtain ⟨element, elementMember, membership⟩ := membership
            cases typed with
            | collection elementsTyped =>
                exact ih element elementMember (elementsHaveType_mem elementsTyped elementMember) membership
            | collectionConstructor _ _ elementsTyped =>
                exact ih element elementMember (elementsHaveType_mem elementsTyped elementMember) membership
          · simp only [parallelLeaves, parallel, if_false, List.mem_singleton] at membership
            exact single membership
  | happly constructor arguments ih =>
      cases arguments with
      | nil =>
          by_cases unit : constructor = declaration.parallelUnitConstructor
          · simp [parallelLeaves, unit] at membership
          · simp only [parallelLeaves, unit, if_false, List.mem_singleton] at membership
            exact ⟨type, membership ▸ typed⟩
      | cons argument arguments =>
          simp only [parallelLeaves, List.mem_singleton] at membership
          exact ⟨type, membership ▸ typed⟩
  | hbvar index =>
      simp only [parallelLeaves, List.mem_singleton] at membership; exact ⟨type, membership ▸ typed⟩
  | hfvar name =>
      simp only [parallelLeaves, List.mem_singleton] at membership; exact ⟨type, membership ▸ typed⟩
  | hlambda binder body ih =>
      simp only [parallelLeaves, List.mem_singleton] at membership; exact ⟨type, membership ▸ typed⟩
  | hmultiLambda arity binders body ih =>
      simp only [parallelLeaves, List.mem_singleton] at membership; exact ⟨type, membership ▸ typed⟩
  | hsubst body replacement ihBody ihReplacement =>
      simp only [parallelLeaves, List.mem_singleton] at membership; exact ⟨type, membership ▸ typed⟩

/-- Resolving one application keeps its declared type. -/
theorem finishResolveApply_hasType
    (witness : LanguageDef.ReflectivePresentationWitness language declaration)
    {free : FreeTypeContext} {bound : List TypeExpr} {constructor : String}
    {arguments : List Pattern} {result : TypeExpr}
    (typed : HasType language free bound (.apply constructor arguments) result) :
    HasType language free bound (finishResolveApply declaration constructor arguments) result := by
  match arguments, typed with
  | [], typed => exact typed
  | first :: second :: rest, typed => exact typed
  | [payload], typed =>
      simp only [finishResolveApply]
      split
      · rename_i quoted
        subst quoted
        split
        · rename_i name exposed
          obtain ⟨resultEq, payloadTyped⟩ := quote_inv witness typed
          obtain ⟨dropType, dropTyped⟩ := parallelLeaves_typed (declaration := declaration) payloadTyped
            (by rw [exposedDrop?_eq_some_iff.mp exposed]; exact List.mem_singleton_self _)
          rw [resultEq]
          exact (drop_inv witness dropTyped).2
        · exact typed
      · exact typed

private theorem resolution_representation
    (declaration : ReflectivePresentationDecl) (parameter : TermParam) (pattern : Pattern)
    (represented : MatchesParameterRepresentation parameter pattern) :
    MatchesParameterRepresentation parameter (resolveQuotes declaration pattern) := by
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
  /-- Resolving quotations preserves every declaration-derived type. -/
  theorem resolveQuotes_hasType
      (witness : LanguageDef.ReflectivePresentationWitness language declaration)
      {free : FreeTypeContext} {bound : List TypeExpr} {pattern : Pattern} {type : TypeExpr}
      (typed : HasType language free bound pattern type) :
      HasType language free bound (resolveQuotes declaration pattern) type := by
    cases typed with
    | bvar lookup => exact .bvar lookup
    | fvar lookup => exact .fvar lookup
    | constructor membership notBare argumentsTyped =>
        exact finishResolveApply_hasType witness
          (.constructor membership notBare (resolveQuotes_arguments witness argumentsTyped))
    | lambda bodyTyped => exact .lambda (resolveQuotes_hasType witness bodyTyped)
    | multiLambda bodyTyped => exact .multiLambda (resolveQuotes_hasType witness bodyTyped)
    | subst bodyTyped valueTyped =>
        exact .subst (resolveQuotes_hasType witness bodyTyped) (resolveQuotes_hasType witness valueTyped)
    | collection elementsTyped => exact .collection (resolveQuotes_elements witness elementsTyped)
    | collectionConstructor membership parameters elementsTyped =>
        exact .collectionConstructor membership parameters (resolveQuotes_elements witness elementsTyped)

  theorem resolveQuotes_arguments
      (witness : LanguageDef.ReflectivePresentationWitness language declaration)
      {free : FreeTypeContext} {bound : List TypeExpr}
      {patterns : List Pattern} {parameters : List TermParam}
      (typed : ArgumentsHaveTypes language free bound patterns parameters) :
      ArgumentsHaveTypes language free bound (resolveQuotesList declaration patterns) parameters := by
    cases typed with
    | nil => exact .nil
    | cons represented expected headTyped tailTyped =>
        exact .cons (resolution_representation _ _ _ represented) expected
          (resolveQuotes_hasType witness headTyped) (resolveQuotes_arguments witness tailTyped)

  theorem resolveQuotes_elements
      (witness : LanguageDef.ReflectivePresentationWitness language declaration)
      {free : FreeTypeContext} {bound : List TypeExpr}
      {patterns : List Pattern} {type : TypeExpr}
      (typed : ElementsHaveType language free bound patterns type) :
      ElementsHaveType language free bound (resolveQuotesList declaration patterns) type := by
    cases typed with
    | nil => exact .nil _ _
    | cons headTyped tailTyped =>
        exact .cons (resolveQuotes_hasType witness headTyped) (resolveQuotes_elements witness tailTyped)
end

private theorem substitution_representation (declaration : ReflectivePresentationDecl)
    (atIndex : Nat → Nat → Pattern) (depth : Nat) (parameter : TermParam) (pattern : Pattern)
    (represented : MatchesParameterRepresentation parameter pattern) :
    MatchesParameterRepresentation parameter (substituteResolved declaration atIndex depth pattern) := by
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

private theorem instantiation_representation (declaration : ReflectivePresentationDecl)
    (depth : Nat) (replacement : Pattern) (parameter : TermParam) (pattern : Pattern)
    (represented : MatchesParameterRepresentation parameter pattern) :
    MatchesParameterRepresentation parameter (instantiate declaration depth replacement pattern) :=
  substitution_representation _ _ _ _ _ (resolution_representation _ _ _ represented)

mutual
  /-- Structural binder elimination on resolved, sealed code keeps the type
  derived from the authored constructor rows. -/
  theorem substituteResolved_hasType
      (witness : LanguageDef.ReflectivePresentationWitness language declaration)
      {free : FreeTypeContext} {bound binders : List TypeExpr}
      {body replacement : Pattern} {result : TypeExpr}
      (typed : HasType language free (binders ++ .base declaration.nameSort :: bound) body result)
      (sealed : binderSafeAt declaration.quoteConstructor
        (binders ++ .base declaration.nameSort :: bound).length body = true)
      (replacementTyped : HasSort language free bound replacement declaration.nameSort) :
      HasType language free (binders ++ bound)
        (substituteResolved declaration
          (fun level index => instantiateBVarAt level replacement (.bvar index))
          binders.length body) result := by
    cases typed with
    | bvar lookup => exact (HasType.bvar lookup).instantiateBVarAt replacementTyped
    | fvar lookup => exact .fvar lookup
    | @constructor _ rule arguments membership notBare argumentsTyped =>
        have sourceTyped := HasType.constructor membership notBare argumentsTyped
        match arguments, argumentsTyped, sealed, sourceTyped with
        | [], argumentsTyped, _, _ =>
            have parametersEmpty : rule.params = [] :=
              List.eq_nil_iff_length_eq_zero.mpr argumentsTyped.length_eq.symm
            exact .constructor membership notBare (by rw [parametersEmpty]; exact .nil)
        | first :: second :: more, argumentsTyped, sealed, _ =>
            have args := substituteResolved_arguments witness argumentsTyped sealed replacementTyped
            rw [substituteResolvedList_eq_map] at args
            simpa [substituteResolved, substituteResolvedList_eq_map] using
              HasType.constructor membership notBare args
        | [first], argumentsTyped, sealed, sourceTyped =>
            have plainTyped : HasType language free (binders ++ bound)
                (.apply rule.label [substituteResolved declaration
                  (fun level index => instantiateBVarAt level replacement (.bvar index))
                  binders.length first]) (.base rule.category) := by
              have firstSealed : binderSafeListAt declaration.quoteConstructor
                  (binders ++ .base declaration.nameSort :: bound).length [first] = true := by
                by_cases quoted : rule.label = declaration.quoteConstructor
                · simp [binderSafeAt, quoted] at sealed
                  simp only [binderSafeListAt, Bool.and_true]
                  exact binderSafeAt_mono _ sealed (Nat.zero_le _)
                · simpa [binderSafeAt, quoted] using sealed
              have args := substituteResolved_arguments witness argumentsTyped firstSealed replacementTyped
              simpa [substituteResolvedList] using HasType.constructor membership notBare args
            by_cases quoted : rule.label = declaration.quoteConstructor
            · have firstClosed : first.isWellScopedAt 0 = true :=
                isWellScopedAt_of_binderSafeAt _ (by simpa [binderSafeAt, quoted] using sealed)
              have wholeClosed : (Pattern.apply rule.label [first]).isWellScopedAt 0 = true := by
                simpa [Pattern.isWellScopedAt, Pattern.isWellScopedListAt] using firstClosed
              simp only [substituteResolved, quoted, if_true]
              rw [← quoted]
              exact closed_remove_binder sourceTyped wholeClosed replacementTyped
            · by_cases dropped : rule.label = declaration.dropConstructor
              · have notQuote : ¬ declaration.dropConstructor = declaration.quoteConstructor :=
                  fun same => quoted (dropped.trans same)
                by_cases hit : matchesBinder declaration binders.length first = true
                · simp only [substituteResolved, dropped, notQuote, hit, if_false, if_true]
                  have dropTyped : HasType language free
                      (binders ++ .base declaration.nameSort :: bound)
                      (.apply declaration.dropConstructor [first]) (.base rule.category) := by
                    simpa only [dropped] using sourceTyped
                  have resultEq := (drop_inv witness dropTyped).1
                  rw [resultEq]
                  have selected : HasSort language free (binders ++ .base declaration.nameSort :: bound)
                      (.bvar binders.length) declaration.nameSort :=
                    .bvar (by simp)
                  exact receive_hasType witness (selected.instantiateBVarAt replacementTyped)
                · simp only [substituteResolved, dropped, notQuote, hit, if_false, if_true,
                    Bool.false_eq_true]
                  simpa only [dropped] using plainTyped
              · simpa [substituteResolved, quoted, dropped] using plainTyped
    | @lambda _ binder body domain codomain bodyTyped =>
        have transformed := substituteResolved_hasType witness (binders := domain :: binders)
          bodyTyped (by simpa [binderSafeAt] using sealed) replacementTyped
        simpa [substituteResolved, List.length_cons, Nat.add_comm] using HasType.lambda transformed
    | @multiLambda _ arity binderNames body domain codomain bodyTyped =>
        have bodyTyped' : HasType language free
            ((List.replicate arity domain ++ binders) ++ .base declaration.nameSort :: bound) body codomain := by
          simpa [List.append_assoc] using bodyTyped
        have transformed := substituteResolved_hasType witness bodyTyped'
          (by simpa [binderSafeAt, List.length_append, List.length_replicate,
            Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using sealed) replacementTyped
        have transformed' : HasType language free
            (List.replicate arity domain ++ (binders ++ bound))
            (substituteResolved declaration
              (fun level index => instantiateBVarAt level replacement (.bvar index))
              (binders.length + arity) body) codomain := by
          simpa [List.append_assoc, List.length_append, List.length_replicate, Nat.add_comm] using transformed
        exact HasType.multiLambda (binders := binderNames) transformed'
    | @subst _ body value domain codomain bodyTyped valueTyped =>
        simp only [binderSafeAt, Bool.and_eq_true] at sealed
        have transformedBody := substituteResolved_hasType witness (binders := domain :: binders)
          bodyTyped (by simpa using sealed.1) replacementTyped
        have transformedValue := substituteResolved_hasType witness valueTyped sealed.2 replacementTyped
        simpa [substituteResolved, List.length_cons, Nat.add_comm] using
          HasType.subst transformedBody transformedValue
    | collection elementsTyped =>
        have elements := substituteResolved_elements witness elementsTyped sealed replacementTyped
        simpa [substituteResolved] using HasType.collection elements
    | collectionConstructor membership parameters elementsTyped =>
        have elements := substituteResolved_elements witness elementsTyped sealed replacementTyped
        simpa [substituteResolved] using HasType.collectionConstructor membership parameters elements

  theorem substituteResolved_arguments
      (witness : LanguageDef.ReflectivePresentationWitness language declaration)
      {free : FreeTypeContext} {bound binders : List TypeExpr}
      {patterns : List Pattern} {parameters : List TermParam} {replacement : Pattern}
      (typed : ArgumentsHaveTypes language free (binders ++ .base declaration.nameSort :: bound)
        patterns parameters)
      (sealed : binderSafeListAt declaration.quoteConstructor
        (binders ++ .base declaration.nameSort :: bound).length patterns = true)
      (replacementTyped : HasSort language free bound replacement declaration.nameSort) :
      ArgumentsHaveTypes language free (binders ++ bound)
        (substituteResolvedList declaration
          (fun level index => instantiateBVarAt level replacement (.bvar index))
          binders.length patterns) parameters := by
    cases typed with
    | nil => exact .nil
    | cons represented expected headTyped tailTyped =>
        simp only [binderSafeListAt, Bool.and_eq_true] at sealed
        exact .cons (substitution_representation _ _ _ _ _ represented) expected
          (substituteResolved_hasType witness headTyped sealed.1 replacementTyped)
          (substituteResolved_arguments witness tailTyped sealed.2 replacementTyped)

  theorem substituteResolved_elements
      (witness : LanguageDef.ReflectivePresentationWitness language declaration)
      {free : FreeTypeContext} {bound binders : List TypeExpr}
      {patterns : List Pattern} {type : TypeExpr} {replacement : Pattern}
      (typed : ElementsHaveType language free (binders ++ .base declaration.nameSort :: bound) patterns type)
      (sealed : binderSafeListAt declaration.quoteConstructor
        (binders ++ .base declaration.nameSort :: bound).length patterns = true)
      (replacementTyped : HasSort language free bound replacement declaration.nameSort) :
      ElementsHaveType language free (binders ++ bound)
        (substituteResolvedList declaration
          (fun level index => instantiateBVarAt level replacement (.bvar index))
          binders.length patterns) type := by
    cases typed with
    | nil => exact .nil _ _
    | cons headTyped tailTyped =>
        simp only [binderSafeListAt, Bool.and_eq_true] at sealed
        exact .cons (substituteResolved_hasType witness headTyped sealed.1 replacementTyped)
          (substituteResolved_elements witness tailTyped sealed.2 replacementTyped)
end

/-- Eliminate a received name below an arbitrary heterogeneous binder prefix
while retaining the type derived from the exact authored constructor rows.
The name-form premise is not used: every drop either receives the selected
name or is substituted through. -/
theorem instantiate_hasType
    (witness : LanguageDef.ReflectivePresentationWitness language declaration)
    {free : FreeTypeContext} {bound binders : List TypeExpr}
    {body replacement : Pattern} {result : TypeExpr}
    (typed : HasType language free (binders ++ .base declaration.nameSort :: bound) body result)
    (sealed : binderSafeAt declaration.quoteConstructor
      (binders ++ .base declaration.nameSort :: bound).length body = true)
    (_names : namesAdmitted declaration body = true)
    (replacementTyped : HasSort language free bound replacement declaration.nameSort) :
    HasType language free (binders ++ bound)
      (instantiate declaration binders.length replacement body) result :=
  substituteResolved_hasType witness (resolveQuotes_hasType witness typed)
    (resolveQuotes_binderSafeAt declaration sealed) replacementTyped

theorem instantiate_arguments_hasType
    (witness : LanguageDef.ReflectivePresentationWitness language declaration)
    {free : FreeTypeContext} {bound binders : List TypeExpr}
    {patterns : List Pattern} {parameters : List TermParam} {replacement : Pattern}
    (typed : ArgumentsHaveTypes language free (binders ++ .base declaration.nameSort :: bound)
      patterns parameters)
    (sealed : binderSafeListAt declaration.quoteConstructor
      (binders ++ .base declaration.nameSort :: bound).length patterns = true)
    (_names : namesAdmittedList declaration patterns = true)
    (replacementTyped : HasSort language free bound replacement declaration.nameSort) :
    ArgumentsHaveTypes language free (binders ++ bound)
      (instantiateList declaration binders.length replacement patterns) parameters := by
  induction patterns generalizing parameters with
  | nil => cases typed; exact .nil
  | cons head tail ih =>
      cases typed with
      | cons represented expected headTyped tailTyped =>
          simp only [binderSafeListAt, Bool.and_eq_true] at sealed
          simp only [namesAdmittedList, Bool.and_eq_true] at _names
          exact .cons (instantiation_representation _ _ _ _ _ represented) expected
            (instantiate_hasType witness headTyped sealed.1 _names.1 replacementTyped)
            (ih tailTyped sealed.2 _names.2)

theorem instantiate_elements_hasType
    (witness : LanguageDef.ReflectivePresentationWitness language declaration)
    {free : FreeTypeContext} {bound binders : List TypeExpr}
    {patterns : List Pattern} {type : TypeExpr} {replacement : Pattern}
    (typed : ElementsHaveType language free (binders ++ .base declaration.nameSort :: bound) patterns type)
    (sealed : binderSafeListAt declaration.quoteConstructor
      (binders ++ .base declaration.nameSort :: bound).length patterns = true)
    (_names : namesAdmittedList declaration patterns = true)
    (replacementTyped : HasSort language free bound replacement declaration.nameSort) :
    ElementsHaveType language free (binders ++ bound)
      (instantiateList declaration binders.length replacement patterns) type := by
  induction patterns with
  | nil => exact .nil _ _
  | cons head tail ih =>
      cases typed with
      | cons headTyped tailTyped =>
          simp only [binderSafeListAt, Bool.and_eq_true] at sealed
          simp only [namesAdmittedList, Bool.and_eq_true] at _names
          exact .cons (instantiate_hasType witness headTyped sealed.1 _names.1 replacementTyped)
            (ih tailTyped sealed.2 _names.2)

#print axioms instantiate_hasType

end Mettapedia.GSLT.LanguageDef.ReflectiveInstantiationTyping
