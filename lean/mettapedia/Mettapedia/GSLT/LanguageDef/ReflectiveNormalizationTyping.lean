import Mettapedia.GSLT.LanguageDef.TypingInversion
import Mettapedia.OSLF.MeTTaIL.ReflectiveInstantiation

/-!
# Authored typing of reflective quote/drop normalization

The existing validation witness supplies the unique quote and drop rows and
their exact argument sorts. Normalization uses those rows inside arbitrary
authored constructor syntax, including binders and generated Cost apparatus.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ReflectiveNormalizationTyping

open WellSorted
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution

variable {language : LanguageDef} {declaration : ReflectivePresentationDecl}

/-- Invert a unary constructor using its uniquely selected authored row. -/
theorem unary_constructor_inv
    {free : FreeTypeContext} {bound : List TypeExpr}
    {constructor : String} {rule : GrammarRule} {parameter : String}
    {argument result : TypeExpr} {payload : Pattern}
    (unique : language.terms.filter (fun candidate => candidate.label == constructor) = [rule])
    (parameters : rule.params = [.simple parameter argument])
    (typed : HasType language free bound (.apply constructor [payload]) result) :
    result = .base rule.category ∧ HasType language free bound payload argument := by
  obtain ⟨actual, member, label, resultEq, -, args⟩ := typed.apply_inv
  have selected : actual ∈ language.terms.filter (fun candidate => candidate.label == constructor) :=
    List.mem_filter.mpr ⟨member, by simp [label]⟩
  rw [unique] at selected
  have same : actual = rule := List.mem_singleton.mp selected
  subst actual
  rw [parameters] at args
  exact ⟨resultEq, args.simple_cons_inv.1⟩

theorem quote_inv (witness : LanguageDef.ReflectivePresentationWitness language declaration)
    {free : FreeTypeContext} {bound : List TypeExpr} {payload : Pattern} {result : TypeExpr}
    (typed : HasType language free bound (.apply declaration.quoteConstructor [payload]) result) :
    result = .base declaration.nameSort ∧
      HasSort language free bound payload declaration.processSort := by
  have inverted := unary_constructor_inv witness.quoteUnique witness.quoteParameters typed
  simpa only [witness.quoteCategory] using inverted

theorem drop_inv (witness : LanguageDef.ReflectivePresentationWitness language declaration)
    {free : FreeTypeContext} {bound : List TypeExpr} {payload : Pattern} {result : TypeExpr}
    (typed : HasType language free bound (.apply declaration.dropConstructor [payload]) result) :
    result = .base declaration.processSort ∧
      HasSort language free bound payload declaration.nameSort := by
  have inverted := unary_constructor_inv witness.dropUnique witness.dropParameters typed
  simpa only [witness.dropCategory] using inverted

/-- The single quote/drop contraction returns a term of its original name
sort. No operational Drop contraction is introduced. -/
theorem finishNormalizeReflective_hasType
    (witness : LanguageDef.ReflectivePresentationWitness language declaration)
    {free : FreeTypeContext} {bound : List TypeExpr} {constructor : String}
    {arguments : List Pattern} {result : TypeExpr}
    (typed : HasType language free bound (.apply constructor arguments) result) :
    HasType language free bound (finishNormalizeReflectiveApply declaration constructor arguments) result := by
  unfold finishNormalizeReflectiveApply
  split
  · rename_i quoted
    have quoted' : constructor = declaration.quoteConstructor := beq_iff_eq.mp quoted
    split
    · rename_i drop name
      split
      · rename_i dropped
        have dropped' : drop = declaration.dropConstructor := beq_iff_eq.mp dropped
        subst constructor
        subst drop
        obtain ⟨resultEq, payloadTyped⟩ := quote_inv witness typed
        rw [resultEq]
        exact (drop_inv witness payloadTyped).2
      · exact typed
    · exact typed
  · exact typed

private theorem normalization_representation
    (declaration : ReflectivePresentationDecl) (parameter : TermParam) (pattern : Pattern)
    (represented : MatchesParameterRepresentation parameter pattern) :
    MatchesParameterRepresentation parameter (normalizeReflective declaration pattern) := by
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
  /-- Reflective normalization preserves every declaration-derived type,
  not just the source calculus's process fragment. -/
  theorem normalizeReflective_hasType
      (witness : LanguageDef.ReflectivePresentationWitness language declaration)
      {free : FreeTypeContext} {bound : List TypeExpr} {pattern : Pattern} {type : TypeExpr}
      (typed : HasType language free bound pattern type) :
      HasType language free bound (normalizeReflective declaration pattern) type := by
    cases typed with
    | bvar lookup => exact .bvar lookup
    | fvar lookup => exact .fvar lookup
    | constructor membership notBare argumentsTyped =>
        exact finishNormalizeReflective_hasType witness
          (.constructor membership notBare (normalizeReflective_arguments witness argumentsTyped))
    | lambda bodyTyped => exact .lambda (normalizeReflective_hasType witness bodyTyped)
    | multiLambda bodyTyped => exact .multiLambda (normalizeReflective_hasType witness bodyTyped)
    | subst bodyTyped valueTyped =>
        exact .subst (normalizeReflective_hasType witness bodyTyped)
          (normalizeReflective_hasType witness valueTyped)
    | collection elementsTyped => exact .collection (normalizeReflective_elements witness elementsTyped)
    | collectionConstructor membership parameters elementsTyped =>
        exact .collectionConstructor membership parameters (normalizeReflective_elements witness elementsTyped)

  theorem normalizeReflective_arguments
      (witness : LanguageDef.ReflectivePresentationWitness language declaration)
      {free : FreeTypeContext} {bound : List TypeExpr}
      {patterns : List Pattern} {parameters : List TermParam}
      (typed : ArgumentsHaveTypes language free bound patterns parameters) :
      ArgumentsHaveTypes language free bound (normalizeReflectiveList declaration patterns) parameters := by
    cases typed with
    | nil => exact .nil
    | cons represented expected headTyped tailTyped =>
        exact .cons (normalization_representation _ _ _ represented) expected
          (normalizeReflective_hasType witness headTyped) (normalizeReflective_arguments witness tailTyped)

  theorem normalizeReflective_elements
      (witness : LanguageDef.ReflectivePresentationWitness language declaration)
      {free : FreeTypeContext} {bound : List TypeExpr}
      {patterns : List Pattern} {type : TypeExpr}
      (typed : ElementsHaveType language free bound patterns type) :
      ElementsHaveType language free bound (normalizeReflectiveList declaration patterns) type := by
    cases typed with
    | nil => exact .nil _ _
    | cons headTyped tailTyped =>
        exact .cons (normalizeReflective_hasType witness headTyped) (normalizeReflective_elements witness tailTyped)
end

#print axioms normalizeReflective_hasType

end Mettapedia.GSLT.LanguageDef.ReflectiveNormalizationTyping
