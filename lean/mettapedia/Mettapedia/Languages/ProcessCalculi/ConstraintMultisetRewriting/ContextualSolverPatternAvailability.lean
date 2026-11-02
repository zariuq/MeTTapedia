import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualSolverCaseAvailability

/-!
# Structural views and typed case availability for normalized equations

Observation views expose the parameter map certified by a structural hole
occurrence. A model preserves both metadata tags, so distinct declarations
with independently presented result sorts can enter the actual typed
flexible-pair recognizer without changing their declaration family.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualSolverPatternAvailability

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualResidual
open ContextualPatternFragment
open ContextualSolverSelect
open ContextualSolverCaseAvailability
open ContextualRigidNormalForm

variable {S : Signature} {V Next : Type} {source : V → MetaArity S} {next : Next → MetaArity S}

inductive Shape (source : V → MetaArity S) : Observation S source → Prop
  | object {Γ : Ctx S} {sort : S.Srt} (position : Var Γ sort) : Shape source (observe (Term.var position))
  | rigid {Γ : Ctx S} {sort : S.Srt} (operator : S.Op sort)
      (fields : Args (signature S source) (S.arity operator) Γ) :
      Shape source (observe (Term.op (.inl operator) fields))
  | hole {Γ : Ctx S} (identity : V)
      (arguments : Args (signature S source) ((source identity).1.map fun sort => ([], sort)) Γ)
      (rho : Ren S (source identity).1 Γ)
      (spine : ∀ sort position, argsToSub arguments sort position = .var (rho sort position))
      (injective : ∀ sort, Function.Injective (rho sort)) :
      Shape source (observe (Term.op (.inr (.mk identity)) arguments))

theorem observation_shape (observation : Observation S source)
    (patterned : Pattern S source observation.2.2) : Shape source observation := by
  rcases observation with ⟨Γ, sort, term⟩
  change Shape source (observe term)
  refine Pattern.rec
    (motive_1 := fun value _ => Shape source (observe value))
    (motive_2 := fun values _ => PatternArgs S source values)
    ?_ ?_ ?_ ?_ ?_ patterned
  · intro context result position
    exact .object position
  · intro context result operator fields _ _
    exact .rigid operator fields
  · intro context identity arguments rho spine injective
    exact .hole identity arguments rho spine injective
  · intro context
    exact .nil
  · intro arities context binders result head tail first _ _ checkedTail
    exact .cons head tail first checkedTail

def flexibleRoot : Observation S source → Bool
  | ⟨_, _, .op (.inr _) _⟩ => true
  | _ => false

theorem normal_has_flexible {equation : Equation (Observation S source)} (normal : EquationNormal source equation) :
    flexibleRoot equation.1 || flexibleRoot equation.2 = true := by
  cases normal with
  | flexLeft key arguments right => rfl
  | flexRight key left arguments => simp [flexibleRoot, observe]

theorem metadata (candidate : Assignment source next) {left right : Observation S source}
    (same : instantiateObservation candidate left = instantiateObservation candidate right) :
    left.1 = right.1 ∧ left.2.1 = right.2.1 := by
  rcases left with ⟨Γ, sort, left⟩
  rcases right with ⟨Δ, result, right⟩
  exact ⟨congrArg (fun observation : Observation S next => observation.1) same,
    congrArg (fun observation : Observation S next => observation.2.1) same⟩

variable [DecidableEq V] [DecidableEq S.Srt] [∀ sort, DecidableEq (S.Op sort)]

theorem hole_object_available (identity : V) {Γ Δ : Ctx S} {sort : S.Srt}
    (arguments : Args (signature S source) ((source identity).1.map fun sort => ([], sort)) Γ)
    (rho : Ren S (source identity).1 Γ)
    (spine : ∀ result position, argsToSub arguments result position = .var (rho result position))
    (injective : ∀ result, Function.Injective (rho result)) (position : Var Δ sort)
    (candidate : Assignment source next)
    (same : instantiateObservation candidate (observe (Term.op (.inr (.mk identity)) arguments)) =
      instantiateObservation candidate (observe (Term.var (S := signature S source) position))) :
    tryEquation (observe (Term.op (.inr (.mk identity)) arguments),
      observe (Term.var (S := signature S source) position)) ≠ none := by
  obtain ⟨contexts, sorts⟩ := metadata candidate same
  dsimp only [observe] at contexts sorts
  subst Δ
  subst sort
  have typed := observe_injective (S := S) (source := next) same
  rw [instantiate_spine candidate identity arguments rho spine] at typed
  change rename (S := signature S next) rho (candidate identity) = Term.var (S := signature S next) position at typed
  obtain ⟨formal, _, mapped⟩ := Mettapedia.OSLF.Binding.rename_eq_variable (S := signature S next)
    rho (candidate identity) position typed
  subst position
  have available := variable_binding_available (S := S) (source := source) identity arguments rho
    (VariableSpines.complete (S := signature S source) _ arguments rho spine) injective formal
  intro declined
  have parts := declined_parts _ _ (declined_equation _ _ declined)
  have leftDeclined := (declined_bindings _ _ parts.2.1).1
  exact available leftDeclined

theorem object_hole_available (identity : V) {Γ Δ : Ctx S} {sort : S.Srt}
    (arguments : Args (signature S source) ((source identity).1.map fun result => ([], result)) Γ)
    (rho : Ren S (source identity).1 Γ)
    (spine : ∀ result position, argsToSub arguments result position = .var (rho result position))
    (injective : ∀ result, Function.Injective (rho result)) (position : Var Δ sort)
    (candidate : Assignment source next)
    (same : instantiateObservation candidate (observe (Term.var (S := signature S source) position)) =
      instantiateObservation candidate (observe (Term.op (.inr (.mk identity)) arguments))) :
    tryEquation (observe (Term.var (S := signature S source) position),
      observe (Term.op (.inr (.mk identity)) arguments)) ≠ none := by
  obtain ⟨contexts, sorts⟩ := metadata candidate same.symm
  dsimp only [observe] at contexts sorts
  subst Δ
  subst sort
  have typed := observe_injective (S := S) (source := next) same.symm
  rw [instantiate_spine candidate identity arguments rho spine] at typed
  change rename (S := signature S next) rho (candidate identity) = Term.var (S := signature S next) position at typed
  obtain ⟨formal, _, mapped⟩ := Mettapedia.OSLF.Binding.rename_eq_variable (S := signature S next)
    rho (candidate identity) position typed
  subst position
  have available := variable_binding_available (S := S) (source := source) identity arguments rho
    (VariableSpines.complete (S := signature S source) _ arguments rho spine) injective formal
  intro declined
  have parts := declined_parts _ _ (declined_equation _ _ declined)
  have rightDeclined := (declined_bindings _ _ parts.2.1).2
  exact available rightDeclined

theorem hole_rigid_available (identity : V) {Γ Δ : Ctx S} {sort : S.Srt}
    (arguments : Args (signature S source) ((source identity).1.map fun result => ([], result)) Γ)
    (rho : Ren S (source identity).1 Γ)
    (spine : ∀ result position, argsToSub arguments result position = .var (rho result position))
    (operator : S.Op sort) (fields : Args (signature S source) (S.arity operator) Δ)
    (candidate : Assignment source next)
    (same : instantiateObservation candidate (observe (Term.op (.inr (.mk identity)) arguments)) =
      instantiateObservation candidate (observe (Term.op (.inl operator) fields))) :
    tryEquation (observe (Term.op (.inr (.mk identity)) arguments), observe (Term.op (.inl operator) fields)) ≠ none := by
  obtain ⟨contexts, sorts⟩ := metadata candidate same
  dsimp only [observe] at contexts sorts
  subst Δ
  subst sort
  intro declined
  exact rigid_available identity arguments rho (VariableSpines.complete _ arguments rho spine) operator fields
    (declined_parts _ _ (declined_equation _ _ declined)).2.2.2.2.1

theorem rigid_hole_available (identity : V) {Γ Δ : Ctx S} {sort : S.Srt}
    (arguments : Args (signature S source) ((source identity).1.map fun result => ([], result)) Γ)
    (rho : Ren S (source identity).1 Γ)
    (spine : ∀ result position, argsToSub arguments result position = .var (rho result position))
    (operator : S.Op sort) (fields : Args (signature S source) (S.arity operator) Δ)
    (candidate : Assignment source next)
    (same : instantiateObservation candidate (observe (Term.op (.inl operator) fields)) =
      instantiateObservation candidate (observe (Term.op (.inr (.mk identity)) arguments))) :
    tryEquation (observe (Term.op (.inl operator) fields), observe (Term.op (.inr (.mk identity)) arguments)) ≠ none := by
  obtain ⟨contexts, sorts⟩ := metadata candidate same.symm
  dsimp only [observe] at contexts sorts
  subst Δ
  subst sort
  intro declined
  exact rigid_available identity arguments rho (VariableSpines.complete _ arguments rho spine) operator fields
    (declined_parts _ _ (declined_equation _ _ declined)).2.2.2.2.2

theorem holes_available (first second : V) {Γ Δ : Ctx S}
    (arguments : Args (signature S source) ((source first).1.map fun result => ([], result)) Γ)
    (remaining : Args (signature S source) ((source second).1.map fun result => ([], result)) Δ)
    (left : Ren S (source first).1 Γ) (right : Ren S (source second).1 Δ)
    (firstSpine : ∀ result position, argsToSub arguments result position = .var (left result position))
    (secondSpine : ∀ result position, argsToSub remaining result position = .var (right result position))
    (candidate : Assignment source next)
    (same : instantiateObservation candidate (observe (Term.op (.inr (.mk first)) arguments)) =
      instantiateObservation candidate (observe (Term.op (.inr (.mk second)) remaining))) :
    tryEquation (observe (Term.op (.inr (.mk first)) arguments),
      observe (Term.op (.inr (.mk second)) remaining)) ≠ none := by
  obtain ⟨contexts, sorts⟩ := metadata candidate same
  dsimp only [observe] at contexts sorts
  subst Δ
  by_cases identical : first = second
  · subst second
    intro declined
    exact same_hole_available first arguments remaining left right
      (VariableSpines.complete _ arguments left firstSpine) (VariableSpines.complete _ remaining right secondSpine)
      (declined_parts _ _ (declined_equation _ _ declined)).2.2.2.1
  · exact equation_available_of_flex _ _ rfl sorts
      (different_hole_available first second identical sorts arguments remaining left right
        (VariableSpines.complete _ arguments left firstSpine) (VariableSpines.complete _ remaining right secondSpine))

theorem equation_available {equation : Equation (Observation S source)} (normal : EquationNormal source equation)
    (first : Pattern S source equation.1.2.2) (second : Pattern S source equation.2.2.2)
    (candidate : Assignment source next)
    (same : instantiateObservation candidate equation.1 = instantiateObservation candidate equation.2) :
    tryEquation equation ≠ none := by
  have flexible := normal_has_flexible normal
  rcases equation with ⟨left, right⟩
  have leftShape := observation_shape left first
  have rightShape := observation_shape right second
  cases leftShape with
  | object position =>
      cases rightShape with
      | object other => cases flexible
      | rigid operator fields => cases flexible
      | hole identity arguments rho spine injective =>
          exact object_hole_available identity arguments rho spine injective position candidate same
  | rigid operator fields =>
      cases rightShape with
      | object position => cases flexible
      | rigid other remaining => cases flexible
      | hole identity arguments rho spine injective =>
          exact rigid_hole_available identity arguments rho spine operator fields candidate same
  | hole identity arguments rho spine injective =>
      cases rightShape with
      | object position => exact hole_object_available identity arguments rho spine injective position candidate same
      | rigid operator fields => exact hole_rigid_available identity arguments rho spine operator fields candidate same
      | hole other remaining sigma otherSpine otherInjective =>
          exact holes_available identity other arguments remaining rho sigma spine otherSpine candidate same

theorem nonempty_normal_pattern_choice (problem : Problem source) (normal : ProblemNormal problem)
    (patterned : ProblemPattern problem) (candidate : Assignment source next) (solved : Models candidate problem)
    (nonempty : problem ≠ []) : ContextualFrameWorklist.choose problem ≠ none := by
  cases problem with
  | nil => exact False.elim (nonempty rfl)
  | cons equation rest =>
      have both := patterned equation List.mem_cons_self
      have available := equation_available (normal equation List.mem_cons_self) both.1 both.2 candidate
        (solved equation List.mem_cons_self)
      intro declined
      unfold ContextualFrameWorklist.choose at declined
      have noSelection := Option.map_eq_none_iff.mp declined
      simp only [ContextualSolverSelect.choose] at noSelection
      split at noSelection
      · cases noSelection
      · rename_i computed
        exact available computed

theorem normal_pattern_saturated_empty (problem : Problem source) (normal : ProblemNormal problem)
    (patterned : ProblemPattern problem) (candidate : Assignment source next) (solved : Models candidate problem)
    (saturated : ContextualFrameWorklist.choose problem = none) : problem = [] := by
  by_contra nonempty
  exact nonempty_normal_pattern_choice problem normal patterned candidate solved nonempty saturated

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualSolverPatternAvailability
