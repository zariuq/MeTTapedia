import Mettapedia.Languages.MeTTa.TermView

/-!
# Reusing partially prepared query fields

A field may already have been normalized or may still carry an outer
environment. Applying a normalized substitution to either representation
gives the same result. The range condition is essential: a one-step map with
unresolved chains does not satisfy the law. This is a semantic model, not a
proof that a particular C binding store computes its normalized denotation.
-/

namespace Mettapedia.Languages.MeTTa.QueryFieldSubstitution

open TermViewCompilation
open Mettapedia.GSLT.LanguageDef.CompiledPlanOpenActivationViewCompilation

/-- Every replacement is already fixed by the same substitution. -/
def StableRange (σ : OpenSubstitution) : Prop :=
  ∀ logicVar value, σ logicVar = some value → substituteOpen σ value = value

theorem compose_self_of_stableRange (σ : OpenSubstitution)
    (stable : StableRange σ) : composeOpen σ σ = σ := by
  funext logicVar
  cases binding : σ logicVar with
  | none => simp [composeOpen, binding]
  | some value => simp [composeOpen, binding, stable logicVar value binding]

theorem normalize_idempotent (σ : OpenSubstitution)
    (stable : StableRange σ) (value : OpenTerm) :
    substituteOpen σ (substituteOpen σ value) = substituteOpen σ value := by
  rw [substituteOpen_comp, compose_self_of_stableRange σ stable]

/-- The Boolean records which coordinates have already been prepared. It
does not restrict the arity, term constructor, or positions of those fields. -/
def prepareFields (σ : OpenSubstitution) : List (Bool × OpenTerm) → List OpenTerm
  | [] => []
  | (prepared, value) :: rest =>
      (if prepared then substituteOpen σ value else value) :: prepareFields σ rest

/-- Normalize every authored coordinate directly. -/
def freshFields (σ : OpenSubstitution) (fields : List (Bool × OpenTerm)) :
    List OpenTerm := fields.map (fun field => substituteOpen σ field.2)

/-- Complete the outstanding outer substitution on the mixed representation. -/
def reusedFields (σ : OpenSubstitution) (fields : List (Bool × OpenTerm)) :
    List OpenTerm := (prepareFields σ fields).map (substituteOpen σ)

theorem reusedFields_eq_freshFields (σ : OpenSubstitution)
    (stable : StableRange σ) (fields : List (Bool × OpenTerm)) :
    reusedFields σ fields = freshFields σ fields := by
  induction fields with
  | nil => rfl
  | cons field rest ih =>
      rcases field with ⟨prepared, value⟩
      cases prepared <;>
        simp [reusedFields, freshFields, prepareFields,
          normalize_idempotent σ stable] at ih ⊢
      all_goals exact ih

/-- Any consumer, including an occurrence-sensitive or failure-producing
consumer, receives the same complete sequence of fields. -/
theorem observe_reusedFields {Result : Type} (observe : List OpenTerm → Result)
    (σ : OpenSubstitution) (stable : StableRange σ)
    (fields : List (Bool × OpenTerm)) :
    observe (reusedFields σ fields) = observe (freshFields σ fields) := by
  rw [reusedFields_eq_freshFields σ stable]

private def x : LogicVariable := ⟨7, 0⟩
private def y : LogicVariable := ⟨7, 1⟩

private def closed : OpenSubstitution := fun logicVar =>
  if logicVar = x then some (.integer 42) else none

example : StableRange closed := by
  intro logicVar value binding
  by_cases h : logicVar = x
  · simp [closed, h] at binding
    subst value
    rfl
  · simp [closed, h] at binding

example : reusedFields closed [(true, .variable x), (false, .variable x)] =
    [.integer 42, .integer 42] := by decide

-- A raw one-step substitution is insufficient when its range has a chain.
private def chain : OpenSubstitution := fun logicVar =>
  if logicVar = x then some (.variable y)
  else if logicVar = y then some (.integer 42) else none

example : reusedFields chain [(true, .variable x)] ≠
    freshFields chain [(true, .variable x)] := by decide

-- Dropping the final substitution loses bindings in an unprepared field.
example : prepareFields closed [(false, .variable x)] ≠
    freshFields closed [(false, .variable x)] := by decide

end Mettapedia.Languages.MeTTa.QueryFieldSubstitution
