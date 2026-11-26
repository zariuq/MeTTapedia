import Mettapedia.Languages.MeTTa.OSLFCore.Bridge
import Mathlib.Data.List.Dedup

/-!
# Typing native Atom schemas

The carrier type of a metavariable is `GroundAtom`: substitution fills
it with an Atom. This is not the type assigned to that Atom by a MeTTa
type assignment. Literal text inside the codec is typed at its declared
carrier, not looked up as an authored constructor.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.SpaceTheory.NativeTyping

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.OSLFCore.Bridge
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst atomFreeVars)
open Mettapedia.OSLF.MeTTaIL.Syntax (GrammarRule LanguageDef Pattern TypeExpr)
open Mettapedia.OSLF.MeTTaIL.Match (applyBindings)
open Mettapedia.GSLT.LanguageDef.WellSorted
  (FreeTypeContext isObjectPattern isObjectPatternList bareCollectionElementType?
    parameterType? matchesParameterRepresentation?)
open Mettapedia.GSLT.LanguageDef.CarrierWellSorted

abbrev atomSort : TypeExpr := .base "GroundAtom"

private def expressionDecl : GrammarRule :=
  { label := "ground-atom-expression-v1", category := "GroundAtom"
    params := [.simple "payload" (.base "GroundList")], syntaxPattern := [] }

private theorem vector_check (free : FreeTypeContext) (bound : List TypeExpr)
    (children : List Pattern) :
    checkHasType GroundData.dataLanguage free bound
        (.collection .vec children none) (.base "GroundList") =
      checkElementsHaveTypes GroundData.dataLanguage free bound children atomSort := by
  rw [checkHasType]
  simp only [Option.isNone, Bool.true_and, Bool.false_or]
  change GroundData.dataLanguage.terms.any (fun decl =>
    match bareCollectionElementType? decl .vec (.base "GroundList") with
    | some sort => checkElementsHaveTypes GroundData.dataLanguage free bound children sort
    | none => false) = _
  have element : (GroundData.dataLanguage.terms.filterMap
      (fun decl => bareCollectionElementType? decl .vec (.base "GroundList"))) = [atomSort] := by
    decide +kernel
  have factor := List.any_filterMap (l := GroundData.dataLanguage.terms)
    (f := fun decl => bareCollectionElementType? decl .vec (.base "GroundList"))
    (p := checkElementsHaveTypes GroundData.dataLanguage free bound children)
  rw [element] at factor
  simp only [List.any_cons, List.any_nil, Bool.or_false] at factor
  conv_rhs => rw [factor]
  apply congrArg (fun pred => GroundData.dataLanguage.terms.any pred)
  funext decl
  cases bareCollectionElementType? decl .vec (.base "GroundList") <;> simp
  all_goals simp

private theorem expression_check (free : FreeTypeContext) (bound : List TypeExpr)
    (children : List Pattern) :
    checkHasType GroundData.dataLanguage free bound
        (.apply "ground-atom-expression-v1" [.collection .vec children none]) atomSort =
      checkElementsHaveTypes GroundData.dataLanguage free bound children atomSort := by
  rw [checkHasType]
  simp only [List.isEmpty_cons, Bool.false_and, Bool.false_or, Bool.and_assoc]
  rw [← List.any_filter]
  have known : GroundData.dataLanguage.terms.filter
      (fun decl => decl.label == "ground-atom-expression-v1") = [expressionDecl] := by
    decide +kernel
  rw [known]
  simp only [List.any_cons, List.any_nil, Bool.or_false]
  change checkArgumentsHaveTypes GroundData.dataLanguage free bound
    [.collection .vec children none] [.simple "payload" (.base "GroundList")] = _
  simp [checkArgumentsHaveTypes, parameterType?, matchesParameterRepresentation?, vector_check]

mutual
/-- The native schema needs precisely its occurring metavariables, each
at the Atom carrier. Unrelated entries in the context have no effect. -/
theorem schema_checked_iff (atom : Atom) (free : FreeTypeContext) (bound : List TypeExpr) :
    checkHasType GroundData.dataLanguage free bound (GroundData.schema atom) atomSort = true ↔
      ∀ name ∈ atomFreeVars atom, free name = some atomSort := by
  cases atom with
  | symbol name =>
    simp [GroundData.schema, GroundData.encode_checked, atomFreeVars]
  | grounded value =>
    simp [GroundData.schema, GroundData.encode_checked, atomFreeVars]
  | var name =>
    simp [GroundData.schema, atomFreeVars, checkHasType, beq_iff_eq]
  | expression children =>
    rw [GroundData.schema, expression_check, schemaList_checked_iff children free bound]
    rfl
termination_by sizeOf atom

theorem schemaList_checked_iff (atoms : List Atom) (free : FreeTypeContext) (bound : List TypeExpr) :
    checkElementsHaveTypes GroundData.dataLanguage free bound (GroundData.schemaList atoms) atomSort = true ↔
      ∀ name ∈ atomFreeVars.atomFreeVarsList atoms, free name = some atomSort := by
  cases atoms with
  | nil => simp [GroundData.schemaList, checkElementsHaveTypes, atomFreeVars.atomFreeVarsList]
  | cons first tail =>
    simp only [GroundData.schemaList, checkElementsHaveTypes, Bool.and_eq_true,
      schema_checked_iff first free bound, schemaList_checked_iff tail free bound,
      atomFreeVars.atomFreeVarsList, List.mem_append]
    constructor
    · rintro ⟨left, right⟩ name (member | member)
      · exact left name member
      · exact right name member
    · intro covers
      exact ⟨fun n h => covers n (.inl h), fun n h => covers n (.inr h)⟩
termination_by sizeOf atoms
end

mutual
theorem schema_isObject (atom : Atom) : isObjectPattern (GroundData.schema atom) = true := by
  cases atom with
  | var => rfl
  | symbol | grounded => simp [GroundData.schema, GroundData.encode_isObject]
  | expression children =>
    simp [GroundData.schema, isObjectPattern, isObjectPatternList, schemaList_isObject children]
termination_by sizeOf atom

theorem schemaList_isObject (atoms : List Atom) :
    isObjectPatternList (GroundData.schemaList atoms) = true := by
  cases atoms with
  | nil => rfl
  | cons head tail =>
    simp [GroundData.schemaList, isObjectPatternList, schema_isObject head, schemaList_isObject tail]
termination_by sizeOf atoms
end

theorem schema_has_type_iff (atom : Atom) (free : FreeTypeContext) (bound : List TypeExpr) :
    HasType GroundData.dataLanguage free bound (GroundData.schema atom) atomSort ↔
      ∀ name ∈ atomFreeVars atom, free name = some atomSort :=
  (checkHasType_eq_true_iff (schema_isObject atom)).symm.trans (schema_checked_iff atom free bound)

/-- A tightly scoped typing context for the two sides of an authored
definition. Repeated occurrences of a variable share its declaration. -/
def schemaContext (lhs rhs : Atom) : List (String × TypeExpr) :=
  ((atomFreeVars lhs ++ atomFreeVars rhs).dedup).map fun name => (name, atomSort)

private theorem lookup_uniform (support : List String) (name : String) :
    (support.map fun n => (n, atomSort)).lookup name =
      if name ∈ support then some atomSort else none := by
  induction support with
  | nil => simp
  | cons first tail ih =>
    by_cases same : name = first
    · subst first
      simp
    · have unequal : (name == first) = false := Bool.eq_false_iff.mpr
        (fun yes => same (beq_iff_eq.mp yes))
      simp [List.lookup, unequal, same, ih]

@[simp] theorem schemaContext_lookup (lhs rhs : Atom) (name : String) :
    (schemaContext lhs rhs).lookup name =
      if name ∈ atomFreeVars lhs ++ atomFreeVars rhs then some atomSort else none := by
  rw [schemaContext, lookup_uniform]
  simp only [List.mem_dedup]

theorem schemaContext_unique (lhs rhs : Atom) :
    ((schemaContext lhs rhs).map Prod.fst).Nodup := by
  simpa [schemaContext, List.map_map, Function.comp_def] using
    (List.nodup_dedup (atomFreeVars lhs ++ atomFreeVars rhs))

theorem definition_sides_typed (lhs rhs : Atom) :
    HasType GroundData.dataLanguage (fun name => (schemaContext lhs rhs).lookup name) []
        (GroundData.schema lhs) atomSort ∧
      HasType GroundData.dataLanguage (fun name => (schemaContext lhs rhs).lookup name) []
        (GroundData.schema rhs) atomSort := by
  constructor
  · apply (schema_has_type_iff lhs _ _).mpr
    intro name occurs
    simp [List.mem_append_left _ occurs]
  · apply (schema_has_type_iff rhs _ _).mpr
    intro name occurs
    simp [List.mem_append_right _ occurs]

/-- Substitution in the native view stays in the closed Atom carrier.
The substitution is the dialect's source binding; this theorem does
not choose how a dialect supplies an unbound output variable. -/
theorem substituted_schema_closed (substitution : Subst) (atom : Atom) :
    HasType GroundData.dataLanguage (fun _ => none) []
      (applyBindings (GroundData.bindingsFor substitution atom) (GroundData.schema atom)) atomSort := by
  rw [GroundData.schema_substitution]
  exact GroundData.encode_has_type (applySubst substitution atom) _ _

section Controls

theorem repeated_variables_need_one_declaration :
    schemaContext (.expression [.var "x", .var "x"]) (.var "x") = [("x", atomSort)] := by
  decide +kernel

theorem dropping_a_variable_is_not_a_typed_declaration :
    ¬ HasType GroundData.dataLanguage (fun _ => none) []
      (GroundData.schema (.expression [.symbol "f", .var "x"])) atomSort := by
  intro typed
  have h := (schema_has_type_iff (.expression [.symbol "f", .var "x"]) _ _).mp typed "x" (by decide)
  cases h

/-- A spelling can even equal a structural label. The declared text
carrier accepts it, while the context-free constructor-reference test
must reject its nullary use at that label's declared nonzero arity. -/
theorem literal_spelling_separates_the_two_checks :
    let spelling : Atom := .symbol "ground-atom-symbol-v1"
    HasType GroundData.dataLanguage (fun _ => none) [] (GroundData.schema spelling) atomSort ∧
      (LanguageDef.validatePatternConstructors "literal"
        GroundData.dataLanguage.terms (GroundData.schema spelling)).isEmpty = false := by
  refine ⟨(schema_has_type_iff _ _ _).mpr ?_, by decide +kernel⟩
  simp [atomFreeVars]

end Controls

end Mettapedia.Languages.MeTTa.SpaceTheory.NativeTyping
