import Mettapedia.GSLT.LanguageDef.WellSorted

/-! Constructor typing from an actual declaration lookup. The certificate
retains the constructor's representation choice, parameter order and sorts;
checking a label alone grants no typing authority. -/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.WellSorted.ConstructorCertificates

open Mettapedia.OSLF.MeTTaIL Syntax

def ordinary (row : GrammarRule) : Bool := match row.bareParams with
  | [.simple _ (.collection _ _)] => false
  | _ => true

theorem ordinary_sound (row : GrammarRule) (checked : ordinary row = true) : ¬ UsesBareCollection row := by
  rintro ⟨name, kind, element, shape⟩
  simp only [ordinary, shape, Bool.false_eq_true] at checked

theorem simple_arguments {language : LanguageDef} {free : FreeTypeContext} {bound : List TypeExpr}
    (parameters : List (String × TypeExpr)) (arguments : List Pattern)
    (typed : List.Forall₂ (fun parameter argument => HasType language free bound argument parameter.2) parameters arguments) :
    ArgumentsHaveTypes language free bound arguments (parameters.map fun parameter => .simple parameter.1 parameter.2) := by
  induction typed with
  | nil => exact .nil
  | cons head tail ih => exact .cons trivial rfl head ih

theorem simple {language : LanguageDef} {free : FreeTypeContext} {bound : List TypeExpr}
    {label sort : String} (parameters : List (String × TypeExpr)) (arguments : List Pattern)
    (declared : (language.terms.find? (fun row => row.label == label)).map
      (fun row => (row.category, row.params, ordinary row)) =
      some (sort, parameters.map (fun parameter => .simple parameter.1 parameter.2), true))
    (typed : List.Forall₂ (fun parameter argument => HasType language free bound argument parameter.2) parameters arguments) :
    HasType language free bound (.apply label arguments) (.base sort) := by
  cases found : language.terms.find? (fun row => row.label == label) with
  | none => simp [found] at declared
  | some row =>
      rw [found] at declared
      have parts := Prod.mk.inj (Option.some.inj declared)
      have parametersAndShape := Prod.mk.inj parts.2
      have member : row ∈ language.terms := List.mem_of_find?_eq_some found
      have name : row.label = label := beq_iff_eq.mp (List.find?_some (p := fun row : GrammarRule => row.label == label) found)
      have args : ArgumentsHaveTypes language free bound arguments row.params :=
        parametersAndShape.1.symm ▸ simple_arguments parameters arguments typed
      have result := HasType.constructor member (ordinary_sound row parametersAndShape.2) args
      simpa only [name, parts.1] using result

end Mettapedia.GSLT.LanguageDef.WellSorted.ConstructorCertificates
