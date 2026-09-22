import Mettapedia.GSLT.LanguageDef.SortedEquationInstance

/-!
# Sorted authored equation instances in a free-variable context

The closed sorted-instance relation checks each authored schema variable at
its declared type under an empty free-variable context. Object terms with
free atoms require the same discipline under an explicit context. This file
changes neither the authored equation matcher nor the existing closed
relation; it records the missing contextual substitution judgment beside them.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.EquationSemantics

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.GSLT.LanguageDef.WellSorted

/-- A substitution respects each declaration in the authored equation's
type context, with free object atoms typed by the ambient context. -/
def SortedBindingsIn (language : LanguageDef) (free : FreeTypeContext)
    (typeContext : List (String × TypeExpr)) (bindings : Bindings) : Prop :=
  ∀ name type, (name, type) ∈ typeContext →
    isObjectPattern (applyBindings bindings (.fvar name)) = true ∧
      HasType language free [] (applyBindings bindings (.fvar name)) type

theorem sortedBindingsIn_empty_iff
    (language : LanguageDef) (typeContext : List (String × TypeExpr))
    (bindings : Bindings) :
    SortedBindingsIn language FreeTypeContext.empty typeContext bindings ↔
      SortedBindings language typeContext bindings := Iff.rfl

/-- A sorted equation instance with an explicit free-variable context.
The matcher and premise derivation are exactly the canonical authored ones;
the extra premise checks only the final schema substitution. -/
inductive OpenSortedEquationInstanceAt
    (free : FreeTypeContext) (base : BasePremiseEvaluator)
    (language : LanguageDef) : Nat → Pattern → Pattern → Prop where
  | forward
      {fuel : Nat} {equation : Equation} {source target : Pattern}
      {initialBindings finalBindings : Bindings} :
      List.Mem equation language.equations →
      initialBindings ∈ matchPattern equation.left source →
      PremisesAt base language fuel initialBindings equation.premises
        finalBindings →
      SortedBindingsIn language free equation.typeContext finalBindings →
      applyBindings finalBindings equation.right = target →
      OpenSortedEquationInstanceAt free base language fuel source target
  | reverse
      {fuel : Nat} {equation : Equation} {source target : Pattern}
      {initialBindings finalBindings : Bindings} :
      List.Mem equation language.equations →
      initialBindings ∈ matchPattern equation.right source →
      PremisesAt base language fuel initialBindings equation.premises
        finalBindings →
      SortedBindingsIn language free equation.typeContext finalBindings →
      applyBindings finalBindings equation.left = target →
      OpenSortedEquationInstanceAt free base language fuel source target

def OpenSortedEquationInstance
    (free : FreeTypeContext) (base : BasePremiseEvaluator)
    (language : LanguageDef) (source target : Pattern) : Prop :=
  ∃ fuel, OpenSortedEquationInstanceAt free base language fuel source target

/-- Explicit typing narrows the existing raw instance relation. -/
theorem equationInstance_of_openSortedEquationInstance
    {free : FreeTypeContext} {base : BasePremiseEvaluator}
    {language : LanguageDef} {source target : Pattern}
    (sorted : OpenSortedEquationInstance free base language source target) :
    EquationInstance base language source target := by
  obtain ⟨fuel, instance'⟩ := sorted
  refine ⟨fuel, ?_⟩
  cases instance' with
  | forward member matched premises _ applied =>
      exact EquationInstanceAt.forward member matched premises applied
  | reverse member matched premises _ applied =>
      exact EquationInstanceAt.reverse member matched premises applied

/-- A type-checked open instance is a generator of the canonical authored
equation theory; this is inclusion, not an identification of the relations. -/
theorem equationEquiv_of_openSortedEquationInstance
    {free : FreeTypeContext} {base : BasePremiseEvaluator}
    {language : LanguageDef} {source target : Pattern}
    (sorted : OpenSortedEquationInstance free base language source target) :
    EquationEquiv base language source target :=
  equationInstance_equivalent
    (equationInstance_of_openSortedEquationInstance sorted)

/-- With no free atoms this is exactly the older closed relation. -/
theorem openSortedEquationInstance_empty_iff_sorted
    {base : BasePremiseEvaluator} {language : LanguageDef}
    {source target : Pattern} :
    OpenSortedEquationInstance FreeTypeContext.empty base language source target ↔
      SortedEquationInstance base language source target := by
  constructor
  · rintro ⟨fuel, instance'⟩
    refine ⟨fuel, ?_⟩
    cases instance' with
    | forward member matched premises sorted applied =>
        exact SortedEquationInstanceAt.forward member matched premises
          ((sortedBindingsIn_empty_iff _ _ _).mp sorted) applied
    | reverse member matched premises sorted applied =>
        exact SortedEquationInstanceAt.reverse member matched premises
          ((sortedBindingsIn_empty_iff _ _ _).mp sorted) applied
  · rintro ⟨fuel, instance'⟩
    refine ⟨fuel, ?_⟩
    cases instance' with
    | forward member matched premises sorted applied =>
        exact OpenSortedEquationInstanceAt.forward member matched premises
          ((sortedBindingsIn_empty_iff _ _ _).mpr sorted) applied
    | reverse member matched premises sorted applied =>
        exact OpenSortedEquationInstanceAt.reverse member matched premises
          ((sortedBindingsIn_empty_iff _ _ _).mpr sorted) applied

#print axioms equationInstance_of_openSortedEquationInstance
#print axioms equationEquiv_of_openSortedEquationInstance
#print axioms openSortedEquationInstance_empty_iff_sorted

end Mettapedia.GSLT.LanguageDef.EquationSemantics
