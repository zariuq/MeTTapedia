import Mathlib.CategoryTheory.PathCategory.Basic

/-! Ordered observations of the edges of a path. -/

set_option autoImplicit false

namespace Quiver.Path

universe u v w

variable {V : Type u} [Quiver.{v} V] {A : Type w}

/-- An edge contributes a list of observations. Path composition preserves
their order and multiplicity. -/
def observations (observe : ∀ {source target : V}, (source ⟶ target) → List A)
    {source : V} : {target : V} → Path source target → List A
  | _, .nil => []
  | _, .cons past edge => observations observe past ++ observe edge

@[simp] theorem observations_nil
    (observe : ∀ {source target : V}, (source ⟶ target) → List A) (source : V) :
    observations observe (Path.nil : Path source source) = [] := rfl

@[simp] theorem observations_cons
    (observe : ∀ {source target : V}, (source ⟶ target) → List A)
    {source middle target : V} (past : Path source middle) (edge : middle ⟶ target) :
    observations observe (past.cons edge) = observations observe past ++ observe edge := rfl

theorem observations_comp
    (observe : ∀ {source target : V}, (source ⟶ target) → List A)
    {source middle target : V} (first : Path source middle) (second : Path middle target) :
    observations observe (first.comp second) =
      observations observe first ++ observations observe second := by
  induction second with
  | nil => simp [Path.comp]
  | cons past edge ih => simp [Path.comp, ih, List.append_assoc]

private def observationsWithSuffix
    (observe : ∀ {source target : V}, (source ⟶ target) → List A)
    {source : V} : {target : V} → Path source target → List A → List A
  | _, .nil, suffix => suffix
  | _, .cons past edge, suffix => observationsWithSuffix observe past (observe edge ++ suffix)

private theorem observationsWithSuffix_eq
    (observe : ∀ {source target : V}, (source ⟶ target) → List A)
    {source target : V} (path : Path source target) (suffix : List A) :
    observationsWithSuffix observe path suffix = observations observe path ++ suffix := by
  induction path generalizing suffix with
  | nil => rfl
  | cons past edge ih =>
      simp only [observationsWithSuffix, observations_cons, ih, List.append_assoc]

private def collectObservations
    (observe : ∀ {source target : V}, (source ⟶ target) → List A)
    {source target : V} (path : Path source target) : List A :=
  observationsWithSuffix observe path []

@[csimp] theorem observations_eq_collect :
    @observations = @collectObservations := by
  funext vertices quiver output observe source target path
  simp only [collectObservations, observationsWithSuffix_eq, List.append_nil]

end Quiver.Path
