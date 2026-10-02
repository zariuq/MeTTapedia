import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TowerInterpretation.SetDefinitions
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Annotated.ConstantFamilies

/-!
# A family of constants has a set model when values satisfy its types and equations

A family of constants declared together (`withFamily`) gives each constant a type and relates
the constants by equations. This module gives the criterion under which the package with the
family has a set model.

**The criterion** (`family_setModel_of_values`): let the package before the family have a set
model at every assignment that agrees with a given one on the names it declares, let the
family's names be new to it, and let a value be given for each constant of the family. At
each assignment that agrees with the base on the earlier names and gives the family's
constants their values: every value lies in the set of the constant's type, and both sides of
every equation have one value at every environment of the equation's telescope. Then the
package with the family has a set model, at every assignment that agrees with the base
extended by the values (`familyConsts`) on the names it declares.

The types of the family may mention its own constants: each type is read at the assignment
that already has all the values. A single definition by equations is the family with one
name (`definition_setModel_of_value`).

Consequence: a closed type with an empty set has no closed term in the package with the
family (`family_no_closed_inhabitant`).

Positive example: the family that declares nothing leaves the model as it is
(`empty_family_setModel`); the constants of set theory over the tower inside the sets are a
family with content (`Instances/TowerInterpretation/AmbientSetTheory.lean`). Negative example:
a family that declares a constant at a type with an empty set has no set model at any
assignment (`family_no_setModel_of_empty`).
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TowerInterpretation

open Presentation Presentation.TypedEquality Presentation.TypedEquality.Annotated
open Mettapedia.Logic.HOL.Embedding

universe u

variable {Head : Type} {heads : Head → ZFSet.{u}}

/-- **The assignment of a family over a base assignment**: the family's constants at their
values, every other name at the base assignment. -/
def familyConsts (base : DeclName → ZFSet.{u}) (decls : DeclName → Option (CTm Head 0))
    (values : DeclName → ZFSet.{u}) : DeclName → ZFSet.{u} := fun c =>
  match decls c with
  | some _ => values c
  | none => base c

theorem familyConsts_declared {base : DeclName → ZFSet.{u}}
    {decls : DeclName → Option (CTm Head 0)} {values : DeclName → ZFSet.{u}} {c : DeclName}
    (declared : decls c ≠ none) : familyConsts base decls values c = values c := by
  unfold familyConsts
  cases found : decls c with
  | none => exact absurd found declared
  | some _ => rfl

theorem familyConsts_undeclared {base : DeclName → ZFSet.{u}}
    {decls : DeclName → Option (CTm Head 0)} {values : DeclName → ZFSet.{u}} {c : DeclName}
    (undeclared : decls c = none) : familyConsts base decls values c = base c := by
  unfold familyConsts
  rw [undeclared]

variable {R : Rules Head} {base : DeclName → ZFSet.{u}}
  {decls : DeclName → Option (CTm Head 0)} {eqs : List (DefiningEquation Head)}

/-- **A family of constants has a set model when values satisfy its types and equations.**
The package before the family has a set model at every assignment that agrees with the base
assignment on the names it declares, and the family's names are new to it. At each such
assignment that gives the family's constants their values: every value lies in the set of the
constant's type, and both sides of every equation have one value at every environment of the
equation's telescope. The model is at every assignment that agrees, on the names the package
with the family declares, with the base assignment extended by the values. -/
theorem family_setModel_of_values (B : ChurchRules R)
    (baseModel : ∀ consts : DeclName → ZFSet.{u},
      (∀ c, B.constantType c ≠ none → consts c = base c) → SetModel heads consts B)
    (new : ∀ c, decls c ≠ none → B.constantType c = none) (values : DeclName → ZFSet.{u})
    (typed : ∀ consts : DeclName → ZFSet.{u},
      (∀ c, B.constantType c ≠ none → consts c = base c) →
      (∀ c, decls c ≠ none → consts c = values c) →
        ∀ {c : DeclName} {T : CTm Head 0}, decls c = some T →
          values c ∈ ev heads consts T Fin.elim0)
    (valid : ∀ consts : DeclName → ZFSet.{u},
      (∀ c, B.constantType c ≠ none → consts c = base c) →
      (∀ c, decls c ≠ none → consts c = values c) →
        ∀ e ∈ eqs, ∀ η : Env.{u} e.arity, Sat heads consts e.telescope η →
          ev heads consts e.left η = ev heads consts e.right η)
    (consts : DeclName → ZFSet.{u})
    (agrees : ∀ c, (withFamily B decls eqs).constantType c ≠ none →
      consts c = familyConsts base decls values c) :
    SetModel heads consts (withFamily B decls eqs) := by
  have agreesBase : ∀ c, B.constantType c ≠ none → consts c = base c := by
    intro c declared
    have undeclared : decls c = none := by
      cases found : decls c with
      | none => rfl
      | some T => exact absurd (new c (by rw [found]; exact Option.some_ne_none T)) declared
    have inSum : (withFamily B decls eqs).constantType c ≠ none := by
      cases found : B.constantType c with
      | none => exact absurd found declared
      | some type =>
        rw [withFamily_base B found]
        exact Option.some_ne_none type
    rw [agrees c inSum, familyConsts_undeclared undeclared]
  have agreesFamily : ∀ c, decls c ≠ none → consts c = values c := by
    intro c declared
    have inSum : (withFamily B decls eqs).constantType c ≠ none := by
      rw [withFamily_declared B (new c declared)]
      exact declared
    rw [agrees c inSum, familyConsts_declared declared]
  have modelB := baseModel consts agreesBase
  refine SetModel.sum modelB
    { universes := { modelB.universes with }
      headEq := modelB.headEq
      constants := fun {c T} declared => ?_
      steps := fun {n Γ l r premises} _ required holds ρ sat => ?_ }
  · have known : decls c = some T := declared
    rw [agreesFamily c (by rw [known]; exact Option.some_ne_none T)]
    exact typed consts agreesBase agreesFamily known
  · obtain ⟨e, member, σ, rfl, rfl, rfl⟩ := required
    have satTele : Sat heads consts e.telescope fun i => ev heads consts (σ i) ρ := fun i => by
      have typedAt := holds _ (mem_telescopePremises.mpr ⟨i, rfl⟩) ρ sat
      rwa [ev_subst] at typedAt
    rw [ev_subst, ev_subst]
    exact valid consts agreesBase agreesFamily e member _ satTele

/-- The model at the base assignment extended by the values. -/
theorem family_setModel_read (B : ChurchRules R)
    (baseModel : ∀ consts : DeclName → ZFSet.{u},
      (∀ c, B.constantType c ≠ none → consts c = base c) → SetModel heads consts B)
    (new : ∀ c, decls c ≠ none → B.constantType c = none) (values : DeclName → ZFSet.{u})
    (typed : ∀ consts : DeclName → ZFSet.{u},
      (∀ c, B.constantType c ≠ none → consts c = base c) →
      (∀ c, decls c ≠ none → consts c = values c) →
        ∀ {c : DeclName} {T : CTm Head 0}, decls c = some T →
          values c ∈ ev heads consts T Fin.elim0)
    (valid : ∀ consts : DeclName → ZFSet.{u},
      (∀ c, B.constantType c ≠ none → consts c = base c) →
      (∀ c, decls c ≠ none → consts c = values c) →
        ∀ e ∈ eqs, ∀ η : Env.{u} e.arity, Sat heads consts e.telescope η →
          ev heads consts e.left η = ev heads consts e.right η) :
    SetModel heads (familyConsts base decls values) (withFamily B decls eqs) :=
  family_setModel_of_values B baseModel new values typed valid _ fun _ _ => rfl

/-- **Consistency**: a closed type whose set is empty has no closed term in a package with a
family whose values satisfy its types and equations. -/
theorem family_no_closed_inhabitant (B : ChurchRules R)
    (baseModel : ∀ consts : DeclName → ZFSet.{u},
      (∀ c, B.constantType c ≠ none → consts c = base c) → SetModel heads consts B)
    (new : ∀ c, decls c ≠ none → B.constantType c = none) (values : DeclName → ZFSet.{u})
    (typed : ∀ consts : DeclName → ZFSet.{u},
      (∀ c, B.constantType c ≠ none → consts c = base c) →
      (∀ c, decls c ≠ none → consts c = values c) →
        ∀ {c : DeclName} {T : CTm Head 0}, decls c = some T →
          values c ∈ ev heads consts T Fin.elim0)
    (valid : ∀ consts : DeclName → ZFSet.{u},
      (∀ c, B.constantType c ≠ none → consts c = base c) →
      (∀ c, decls c ≠ none → consts c = values c) →
        ∀ e ∈ eqs, ∀ η : Env.{u} e.arity, Sat heads consts e.telescope η →
          ev heads consts e.left η = ev heads consts e.right η)
    {T : CTm Head 0}
    (empty : ∀ z, z ∉ ev heads (familyConsts base decls values) T Fin.elim0) (t : CTm Head 0) :
    ¬ CTyped (withFamily B decls eqs) .nil t T :=
  CDerivable.no_closed_inhabitant (family_setModel_read B baseModel new values typed valid)
    empty t

/-- Positive example: the family that declares nothing has the model of the package before
it. -/
theorem empty_family_setModel (B : ChurchRules R)
    (baseModel : ∀ consts : DeclName → ZFSet.{u},
      (∀ c, B.constantType c ≠ none → consts c = base c) → SetModel heads consts B) :
    SetModel heads base
      (withFamily B (fun _ => (none : Option (CTm Head 0))) ([] : List (DefiningEquation Head))) :=
  family_setModel_of_values B baseModel (fun _ declared => absurd rfl declared) base
    (fun _ _ _ {_ T} (declared : (none : Option (CTm Head 0)) = some T) => nomatch declared)
    (fun _ _ _ _ member => absurd member List.not_mem_nil) base fun _ _ => rfl

/-- Negative example: **a family that declares a constant at a type with an empty set has no
set model**, at any assignment. -/
theorem family_no_setModel_of_empty (B : ChurchRules R) {c : DeclName} {T : CTm Head 0}
    (new : B.constantType c = none) (declared : decls c = some T)
    (consts : DeclName → ZFSet.{u}) (empty : ∀ z, z ∉ ev heads consts T Fin.elim0) :
    ¬ SetModel heads consts (withFamily B decls eqs) := fun model =>
  empty _ (model.constants ((withFamily_declared B new).trans declared))

end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TowerInterpretation
