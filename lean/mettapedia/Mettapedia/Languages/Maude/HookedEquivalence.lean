import Mettapedia.Languages.Maude.Semantics

/-! Equations with an explicit imported primitive boundary. Conditional
premises use this whole relation, including imported equations and hooks.
The ordinary equation theory embeds by choosing no hook steps. -/

set_option autoImplicit false

namespace Mettapedia.Languages.Maude

abbrev EquationHook := VariableContext → String → Term → Term → Prop

mutual
inductive HookedEquivalent (theory : Theory) (hook : EquationHook)
    (context : VariableContext) : String → Term → Term → Prop where
  | refl {term : Term} {sort : String} : HasSort theory.signature context term sort →
      HookedEquivalent theory hook context sort term term
  | symm {sort : String} {first second : Term} :
      HookedEquivalent theory hook context sort first second →
      HookedEquivalent theory hook context sort second first
  | trans {sort : String} {first middle last : Term} :
      HookedEquivalent theory hook context sort first middle →
      HookedEquivalent theory hook context sort middle last →
      HookedEquivalent theory hook context sort first last
  | argument {hole sort : String} (frame : ArgumentContext theory.signature context hole sort)
      {first second : Term} : HookedEquivalent theory hook context hole first second →
      HookedEquivalent theory hook context sort (frame.plug first) (frame.plug second)
  | algebra {sort : String} {first second : Term} :
      AlgebraStep theory.signature context sort first second →
      HookedEquivalent theory hook context sort first second
  | equation {row : Row} {sort : String} (assignment : Valuation) :
      row ∈ theory.equations → row.check theory.signature = true →
      HasSort theory.signature row.usedContext row.left sort →
      HasSort theory.signature row.usedContext row.right sort →
      TypedValuation theory.signature context row.usedContext assignment →
      HookedConditions theory hook context assignment row.conditions →
      HookedEquivalent theory hook context sort
        (row.left.substitute assignment) (row.right.substitute assignment)
  | primitive {sort : String} {source target : Term} :
      HasSort theory.signature context source sort → HasSort theory.signature context target sort →
      hook context sort source target → HookedEquivalent theory hook context sort source target

inductive HookedConditions (theory : Theory) (hook : EquationHook)
    (context : VariableContext) : Valuation → List Condition → Prop where
  | nil (assignment : Valuation) : HookedConditions theory hook context assignment []
  | cons {assignment : Valuation} {condition : Condition} {rest : List Condition} {sort : String} :
      HookedEquivalent theory hook context sort
        (condition.left.substitute assignment) (condition.right.substitute assignment) →
      HookedConditions theory hook context assignment rest →
      HookedConditions theory hook context assignment (condition :: rest)
end

theorem Equivalent.toHooked {theory : Theory} {context : VariableContext} {sort : String}
    {source target : Term} (equivalent : Equivalent theory context sort source target)
    (hook : EquationHook) : HookedEquivalent theory hook context sort source target := by
  refine Equivalent.rec
    (motive_1 := fun sort source target _ => HookedEquivalent theory hook context sort source target)
    (motive_2 := fun assignment conditions _ => HookedConditions theory hook context assignment conditions)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ equivalent
  · intro _ _ typed
    exact .refl typed
  · intro _ _ _ _ ih
    exact .symm ih
  · intro _ _ _ _ _ _ first last
    exact .trans first last
  · intro _ _ frame _ _ _ ih
    exact .argument frame ih
  · intro _ _ _ step
    exact .algebra step
  · intro row sort assignment member checked left right typed _ conditions
    exact .equation assignment member checked left right typed conditions
  · intro assignment
    exact .nil assignment
  · intro assignment condition rest sort _ _ first last
    exact .cons first last

theorem HookedEquivalent.toOrdinary {theory : Theory} {context : VariableContext} {sort : String}
    {source target : Term}
    (equivalent : HookedEquivalent theory (fun _ _ _ _ => False) context sort source target) :
    Equivalent theory context sort source target := by
  refine HookedEquivalent.rec
    (motive_1 := fun sort source target _ => Equivalent theory context sort source target)
    (motive_2 := fun assignment conditions _ => Conditions theory context assignment conditions)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ equivalent
  · intro _ _ typed
    exact .refl typed
  · intro _ _ _ _ ih
    exact .symm ih
  · intro _ _ _ _ _ _ first last
    exact .trans first last
  · intro _ _ frame _ _ _ ih
    exact .argument frame ih
  · intro _ _ _ step
    exact .algebra step
  · intro row sort assignment member checked left right typed _ conditions
    exact .equation assignment member checked left right typed conditions
  · intro _ _ _ _ _ impossible
    exact impossible.elim
  · intro assignment
    exact .nil assignment
  · intro _ _ _ _ _ _ first last
    exact .cons first last

end Mettapedia.Languages.Maude
