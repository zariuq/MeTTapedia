import Mettapedia.OSLF.Syntax.DeterministicGSOSBehaviour

/-!
# Independently authored complete guarded rules

A guard records exactly which input actions are available. Its variables
are the original arguments and the available derivatives, all at their
declared sorts. A conclusion is an existing finite constructor term over
those variables. Guards and variable families may be infinite; this is a
complete guarded presentation, distinct from finite-premise GSOS rules.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.DeterministicGSOS

open CategoryTheory Mettapedia.TypeTheory

universe u

variable {S : Signature.{u}} (Actions : S.Srt → Type u)

/-- An individually addressed input action. -/
abbrev Address {sort : S.Srt} (operator : S.Operator sort) :=
  Σ position : S.Position operator, Actions (S.argument operator position)

/-- A complete action-availability guard. -/
abbrev Guard {sort : S.Srt} (operator : S.Operator sort) :=
  Address Actions operator → Bool

/-- Typed names available to the independently authored conclusion. -/
inductive RuleVariable {sort : S.Srt} (operator : S.Operator sort)
    (guard : Guard Actions operator) : S.Srt → Type u where
  | original (position : S.Position operator) :
      RuleVariable operator guard (S.argument operator position)
  | derivative (address : Address Actions operator) (enabled : guard address = true) :
      RuleVariable operator guard (S.argument operator address.1)

/-- The generic indexed variable family of a complete guard. -/
abbrev ruleVariables {sort : S.Srt} (operator : S.Operator sort)
    (guard : Guard Actions operator) : S.Families :=
  fun _ index => RuleVariable Actions operator guard index

/-- One target term for each enabled output action, at every complete guard. -/
abbrev GuardedSchemas :=
  (sort : S.Srt) → (operator : S.Operator sort) →
    (guard : Guard Actions operator) → Actions sort →
      Option (S.Term (ruleVariables Actions operator guard) sort)

/-- Read the complete availability pattern of independently supplied inputs. -/
def inputGuard {X : S.Families} {sort : S.Srt} {operator : S.Operator sort}
    (arguments : BehaviourArguments S Actions X operator) : Guard Actions operator :=
  fun address => ((arguments address.1).2 address.2).isSome

/-- Distinct original and derivative variables form the generic input. -/
noncomputable def genericArguments {sort : S.Srt} (operator : S.Operator sort)
    (guard : Guard Actions operator) :
    BehaviourArguments S Actions (ruleVariables Actions operator guard) operator :=
  fun position => (.original position, fun action =>
    if enabled : guard ⟨position, action⟩ = true then
      some (.derivative ⟨position, action⟩ enabled)
    else none)

theorem inputGuard_generic {sort : S.Srt} (operator : S.Operator sort)
    (guard : Guard Actions operator) :
    inputGuard Actions (genericArguments Actions operator guard) = guard := by
  funext address
  rcases address with ⟨position, action⟩
  cases available : guard ⟨position, action⟩ <;>
    simp [inputGuard, genericArguments, available]

/-- An input assignment interprets each derivative by its exact supplied value. -/
noncomputable def assignment {X : S.Families} {sort : S.Srt}
    {operator : S.Operator sort}
    (arguments : BehaviourArguments S Actions X operator) :
    ruleVariables Actions operator (inputGuard Actions arguments) ⟶ X :=
  fun base index => ↾(fun name =>
    match base, name with
    | .unit, .original position => (arguments position).1
    | .unit, .derivative ⟨position, action⟩ enabled =>
        ((arguments position).2 action).get enabled)

/-- The same assignment against an independently named matching guard. -/
noncomputable def assignmentAt {X : S.Families} {sort : S.Srt}
    {operator : S.Operator sort} (guard : Guard Actions operator)
    (arguments : BehaviourArguments S Actions X operator)
    (matching : inputGuard Actions arguments = guard) :
    ruleVariables Actions operator guard ⟶ X :=
  fun base index => ↾(fun name =>
    match base, name with
    | .unit, .original position => (arguments position).1
    | .unit, .derivative ⟨position, action⟩ enabled =>
        ((arguments position).2 action).get
          (by exact (congrFun matching ⟨position, action⟩).trans enabled))

theorem assignmentAt_self {X : S.Families} {sort : S.Srt}
    {operator : S.Operator sort}
    (arguments : BehaviourArguments S Actions X operator) :
    assignmentAt Actions (inputGuard Actions arguments) arguments rfl =
      assignment Actions arguments := by
  funext base index
  apply ConcreteCategory.hom_ext
  intro name
  cases base
  cases name <;> rfl

theorem assignmentAt_generic {sort : S.Srt} (operator : S.Operator sort)
    (guard : Guard Actions operator) :
    assignmentAt Actions guard (genericArguments Actions operator guard)
      (inputGuard_generic Actions operator guard) =
      𝟙 (ruleVariables Actions operator guard) := by
  funext base index
  apply ConcreteCategory.hom_ext
  intro name
  cases base
  cases name with
  | original position => rfl
  | derivative address enabled =>
      simp [assignmentAt, genericArguments]

/-- Substitution of the generic source and complete behavior recovers the input. -/
theorem generic_assignment {X : S.Families} {sort : S.Srt}
    {operator : S.Operator sort}
    (arguments : BehaviourArguments S Actions X operator) :
    (fun position =>
      (assignment Actions arguments PUnit.unit _
        (genericArguments Actions operator (inputGuard Actions arguments) position).1,
       behaviourMap S Actions (assignment Actions arguments) PUnit.unit _
        (genericArguments Actions operator (inputGuard Actions arguments) position).2)) =
      arguments := by
  funext position
  apply Prod.ext
  · rfl
  · funext action
    cases read : (arguments position).2 action <;>
      simp [genericArguments, inputGuard, assignment, behaviourMap, read]

/-- Availability is unchanged by any variable map, including identifications. -/
theorem inputGuard_map {X Y : S.Families} (mapping : X ⟶ Y)
    {sort : S.Srt} {operator : S.Operator sort}
    (arguments : BehaviourArguments S Actions X operator) :
    inputGuard Actions (fun position =>
      (mapping PUnit.unit _ (arguments position).1,
       behaviourMap S Actions mapping PUnit.unit _ (arguments position).2)) =
      inputGuard Actions arguments := by
  funext address
  cases read : (arguments address.1).2 address.2 <;>
    simp [inputGuard, behaviourMap, read]

/-- Increasing the available-variable family maps each name without changing it. -/
def variableInclusion {sort : S.Srt} {operator : S.Operator sort}
    {first second : Guard Actions operator}
    (enabled : ∀ address, first address = true → second address = true) :
    ruleVariables Actions operator first ⟶ ruleVariables Actions operator second :=
  fun _ _ => ↾(fun name => match name with
    | .original position => .original position
    | .derivative address present => .derivative address (enabled address present))

end Mettapedia.OSLF.DeterministicGSOS
