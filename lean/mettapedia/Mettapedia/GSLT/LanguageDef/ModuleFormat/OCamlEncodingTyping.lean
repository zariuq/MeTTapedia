import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlValueReading
import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlPatternShapes
import Mettapedia.GSLT.LanguageDef.WellSorted
import Mathlib.Tactic.IntervalCases

/-! Compact O0 values inhabit the actual authored IR sorts. Constructor
certificates select the module's declared rows by label; they do not install
a parallel grammar or infer typing from successful execution.
-/

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation

open Mettapedia.Languages
open Mettapedia.OSLF.MeTTaIL Syntax
open Mettapedia.GSLT.LanguageDef.WellSorted

def constructor? (label : String) : Option GrammarRule := baseLanguage.terms.find? (fun row => row.label == label)

theorem declared_constructor_typed {language : LanguageDef} (terms : language.terms = baseLanguage.terms)
    {free : FreeTypeContext} {bound : List TypeExpr} {label sort : String} {parameters : List TermParam}
    {arguments : List Pattern}
    (declared : (constructor? label).map (fun row => (row.category, row.params)) = some (sort, parameters))
    (ordinary : ∀ row, constructor? label = some row → ¬ UsesBareCollection row)
    (typed : ArgumentsHaveTypes language free bound arguments parameters) :
    HasType language free bound (node label arguments) (.base sort) := by
  cases found : constructor? label with
  | none => simp [found] at declared
  | some row =>
      have fields : (row.category, row.params) = (sort, parameters) := by simpa only [found, Option.map_some, Option.some.injEq] using declared
      have fieldParts := Prod.mk.inj fields
      have rowMember : row ∈ baseLanguage.terms := List.mem_of_find?_eq_some found
      have rowLabel : row.label = label := beq_iff_eq.mp (List.find?_some
        (p := fun row : GrammarRule => row.label == label) found)
      have actualTyped : ArgumentsHaveTypes language free bound arguments row.params := fieldParts.2.symm ▸ typed
      have result := HasType.constructor (language := language) (free := free) (bound := bound)
        (by rw [terms]; exact rowMember) (ordinary row found) actualTyped
      simpa only [node, rowLabel, fieldParts.1] using result

theorem constructor_not_bare {label : String} {parameters : List TermParam} {sort : String}
    (declared : (constructor? label).map (fun row => (row.category, row.params, row.bareParams)) =
      some (sort, parameters, parameters))
    (notCollection : ¬ ∃ name kind element, parameters = [.simple name (.collection kind element)]) :
    ∀ row, constructor? label = some row → ¬ UsesBareCollection row := by
  intro row found bare
  rw [found] at declared
  have fields := Option.some.inj declared
  obtain ⟨name, kind, element, shape⟩ := bare
  apply notCollection
  exact ⟨name, kind, element, (congrArg (fun fields => fields.2.2) fields).symm.trans shape⟩

theorem constructor_typed_certificate {language : LanguageDef} (terms : language.terms = baseLanguage.terms)
    {free : FreeTypeContext} {bound : List TypeExpr} {label sort : String} {parameters bare : List TermParam}
    {arguments : List Pattern}
    (declared : (constructor? label).map (fun row => (row.category, row.params, row.bareParams)) = some (sort, parameters, bare))
    (notCollection : ¬ ∃ name kind element, bare = [.simple name (.collection kind element)])
    (typed : ArgumentsHaveTypes language free bound arguments parameters) :
    HasType language free bound (node label arguments) (.base sort) := by
  cases found : constructor? label with
  | none => simp [found] at declared
  | some row =>
      have fields : (row.category, row.params, row.bareParams) = (sort, parameters, bare) := by
        simpa only [found, Option.map_some, Option.some.injEq] using declared
      have fieldParts := Prod.mk.inj fields
      have parameterParts := Prod.mk.inj fieldParts.2
      have rowMember : row ∈ baseLanguage.terms := List.mem_of_find?_eq_some found
      have rowLabel : row.label = label := beq_iff_eq.mp (List.find?_some
        (p := fun row : GrammarRule => row.label == label) found)
      have ordinary : ¬ UsesBareCollection row := by
        rintro ⟨name, kind, element, shape⟩
        exact notCollection ⟨name, kind, element, parameterParts.2.symm.trans shape⟩
      have result := HasType.constructor (language := language) (free := free) (bound := bound)
        (by rw [terms]; exact rowMember) ordinary (parameterParts.1.symm ▸ typed)
      simpa only [node, rowLabel, fieldParts.1] using result

theorem typed_node_open {language : LanguageDef} {free : FreeTypeContext} {bound : List TypeExpr}
    {pattern : Pattern} {type : TypeExpr} (shape : GeneralFirstOrderProjection.VectorFirstOrder pattern)
    (typed : HasType language free bound pattern type) : OpenPatternWellSorted language free bound type pattern :=
  ⟨typed, GeneralRuleBindingInference.vector_canonical shape, GeneralRuleBindingInference.vector_object shape, typed.isWellScopedAt⟩

theorem simple_arguments_typed {language : LanguageDef} {free : FreeTypeContext} {bound : List TypeExpr}
    (parameters : List (String × TypeExpr)) (arguments : List Pattern)
    (typed : List.Forall₂ (fun parameter argument => HasType language free bound argument parameter.2) parameters arguments) :
    ArgumentsHaveTypes language free bound arguments (parameters.map fun parameter => .simple parameter.1 parameter.2) := by
  induction typed with
  | nil => exact .nil
  | @cons parameter argument parameters arguments head tail ih =>
      exact .cons trivial rfl head ih

theorem simple_constructor_typed {language : LanguageDef} (terms : language.terms = baseLanguage.terms)
    {free : FreeTypeContext} {bound : List TypeExpr} {label sort : String}
    (parameters : List (String × TypeExpr)) (arguments : List Pattern) (bare : List TermParam)
    (declared : (constructor? label).map (fun row => (row.category, row.params, row.bareParams)) =
      some (sort, parameters.map (fun parameter => .simple parameter.1 parameter.2), bare))
    (notCollection : ¬ ∃ name kind element, bare = [.simple name (.collection kind element)])
    (typed : List.Forall₂ (fun parameter argument => HasType language free bound argument parameter.2) parameters arguments) :
    HasType language free bound (node label arguments) (.base sort) :=
  constructor_typed_certificate terms declared notCollection (simple_arguments_typed parameters arguments typed)

def ordinaryConstructor (row : GrammarRule) : Bool := match row.bareParams with
  | [.simple _ (.collection _ _)] => false
  | _ => true

theorem ordinaryConstructor_sound (row : GrammarRule) (checked : ordinaryConstructor row = true) :
    ¬ UsesBareCollection row := by
  rintro ⟨name, kind, element, shape⟩
  simp only [ordinaryConstructor, shape, Bool.false_eq_true] at checked

theorem nonbare_constructor_typed {language : LanguageDef} (terms : language.terms = baseLanguage.terms)
    {free : FreeTypeContext} {bound : List TypeExpr} {label sort : String}
    (parameters : List (String × TypeExpr)) (arguments : List Pattern)
    (declared : (constructor? label).map (fun row => (row.category, row.params, ordinaryConstructor row)) =
      some (sort, parameters.map (fun parameter => .simple parameter.1 parameter.2), true))
    (typed : List.Forall₂ (fun parameter argument => HasType language free bound argument parameter.2) parameters arguments) :
    HasType language free bound (node label arguments) (.base sort) := by
  apply declared_constructor_typed terms
  · cases found : constructor? label with
    | none => simp [found] at declared
    | some row =>
        rw [found] at declared
        have parts := Prod.mk.inj (Option.some.inj declared)
        exact by simp only [Option.map_some]; exact congrArg some (Prod.ext parts.1 (Prod.mk.inj parts.2).1)
  · intro row found
    rw [found] at declared
    exact ordinaryConstructor_sound row (Prod.mk.inj (Prod.mk.inj (Option.some.inj declared)).2).2
  · exact simple_arguments_typed parameters arguments typed

theorem nibble_typed (language : LanguageDef) (terms : language.terms = baseLanguage.terms)
    (free : FreeTypeContext) (bound : List TypeExpr) (digit : Nat) (bounded : digit < 16) :
    HasType language free bound (node ("R16Nibble" ++ toString digit)) (.base "R16Nibble") := by
  interval_cases digit <;>
    exact constructor_typed_certificate (label := _) (parameters := []) (bare := [])
      terms (by decide +kernel) (by simp) .nil

theorem digits_typed (language : LanguageDef) (terms : language.terms = baseLanguage.terms)
    (free : FreeTypeContext) (bound : List TypeExpr) (number : Nat) :
    HasType language free bound (digits number) (.collection .vec (.base "R16Nibble")) := by
  apply HasType.collection
  have each : ∀ digit ∈ Nat.digits 16 number, digit < 16 :=
    fun digit member => Nat.digits_lt_base (by decide) member
  generalize Nat.digits 16 number = items at *
  induction items with
  | nil => exact .nil _ _
  | cons first rest ih =>
      exact .cons (nibble_typed language terms free bound first (each first List.mem_cons_self))
        (ih (fun digit member => each digit (List.mem_cons_of_mem first member)))

theorem code_typed (language : LanguageDef) (terms : language.terms = baseLanguage.terms)
    (free : FreeTypeContext) (bound : List TypeExpr) (reference : Nat) :
    HasType language free bound (code reference) (.base "MlCode") := by
  exact constructor_typed_certificate (parameters := [.simple "digits" (.collection .vec (.base "R16Nibble"))])
    (bare := []) terms (by decide +kernel) (by simp)
    (.cons trivial rfl (digits_typed language terms free bound reference) .nil)

#print axioms nibble_typed
#print axioms digits_typed
#print axioms code_typed

end Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation
