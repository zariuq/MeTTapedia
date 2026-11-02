import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualSolverPatternAvailability

/-!
# Every unrefuted nonempty normal pattern queue has an actual solver choice

Matching context and sort tags follow from the rigid normal form. A missing
object-variable preimage is detected by the executable scope refuter; when
that refuter declines, the actual partial inverse supplies the formal
variable needed by binding recovery. No higher-order model is supplied to
these availability theorems.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualUnrefutedPatternAvailability

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualResidual
open ContextualPatternFragment
open ContextualRigidNormalForm
open ContextualSolverPatternAvailability
open ContextualSolverCaseAvailability
open ContextualSolverSelect

variable {S : Signature} {V : Type} {source : V → MetaArity S}

theorem normal_metadata {equation : Equation (Observation S source)} (normal : EquationNormal source equation) :
    equation.1.1 = equation.2.1 ∧ equation.1.2.1 = equation.2.2.1 := by
  cases normal <;> exact ⟨rfl, rfl⟩

private theorem orElse_none {α : Type} (first : Option α) (fallback : Unit → Option α) :
    first.orElse fallback = none ↔ first = none ∧ fallback () = none := by
  cases first <;> simp only [Option.orElse, reduceCtorEq, false_and, true_and]

variable [DecidableEq V] [DecidableEq S.Srt]

theorem declined_refutations {Γ : Ctx S} {sort : S.Srt} (left right : Term (signature S source) Γ sort)
    (declined : ContextualEquationRefutation.tryTerms left right = none) :
    ContextualEquationRefutation.tryLeft left right = none ∧ ContextualEquationRefutation.tryLeft right left = none := by
  simpa only [ContextualEquationRefutation.tryTerms, orElse_none, Option.map_eq_none_iff] using declined

theorem declined_refutation_equation {Γ : Ctx S} {sort : S.Srt} (left right : Term (signature S source) Γ sort)
    (declined : ContextualEquationRefutation.tryEquation (observe left, observe right) = none) :
    ContextualEquationRefutation.tryTerms left right = none := by
  simpa [ContextualEquationRefutation.tryEquation, observe] using declined

theorem missing_variable_refuter (identity : V) {Γ : Ctx S}
    (arguments : Args (signature S source) ((source identity).1.map fun sort => ([], sort)) Γ)
    (rho : Ren S (source identity).1 Γ)
    (recognized : VariableSpines.recognize (S := signature S source) (source identity).1 arguments = some rho)
    (position : Var Γ (source identity).2)
    (missing : RenamingInverse.inverse (S := signature S source) rho _ position = none) :
    ContextualEquationRefutation.tryLeft (Term.op (.inr (.mk identity)) arguments)
      (Term.var (S := signature S source) position) ≠ none := by
  intro declined
  simp only [ContextualEquationRefutation.tryLeft] at declined
  split at declined
  · rename_i computed
    cases recognized.symm.trans computed
  · rename_i chosen computed
    have same : chosen = rho := Option.some.inj (computed.symm.trans recognized)
    subst chosen
    split at declined
    · cases declined
    · rename_i impossible
      exact impossible missing

theorem preimage_of_unrefuted (identity : V) {Γ : Ctx S}
    (arguments : Args (signature S source) ((source identity).1.map fun sort => ([], sort)) Γ)
    (rho : Ren S (source identity).1 Γ)
    (recognized : VariableSpines.recognize (S := signature S source) (source identity).1 arguments = some rho)
    (position : Var Γ (source identity).2)
    (unrefuted : ContextualEquationRefutation.tryLeft (Term.op (.inr (.mk identity)) arguments)
      (Term.var (S := signature S source) position) = none) :
    ∃ formal, rho (source identity).2 formal = position := by
  cases found : RenamingInverse.inverse (S := signature S source) rho _ position with
  | none => exact False.elim (missing_variable_refuter identity arguments rho recognized position found unrefuted)
  | some formal => exact ⟨formal, RenamingInverse.inverse_sound (S := signature S source) rho _ position formal found⟩

theorem head_unrefuted {equation : Equation (Observation S source)} {rest : Problem source}
    (unrefuted : ContextualEquationRefutation.choose (equation :: rest) = none) :
    ContextualEquationRefutation.tryEquation equation = none := by
  cases checked : ContextualEquationRefutation.tryEquation equation with
  | none => rfl
  | some impossible => simp only [ContextualEquationRefutation.choose, checked, reduceCtorEq] at unrefuted

variable [∀ sort, DecidableEq (S.Op sort)]

theorem hole_object_available (identity : V) {Γ Δ : Ctx S} {sort : S.Srt}
    (arguments : Args (signature S source) ((source identity).1.map fun result => ([], result)) Γ)
    (rho : Ren S (source identity).1 Γ)
    (spine : ∀ result position, argsToSub arguments result position = .var (rho result position))
    (injective : ∀ result, Function.Injective (rho result)) (position : Var Δ sort)
    (contexts : Γ = Δ) (sorts : (source identity).2 = sort)
    (unrefuted : ContextualEquationRefutation.tryEquation (observe (Term.op (.inr (.mk identity)) arguments),
      observe (Term.var (S := signature S source) position)) = none) :
    tryEquation (observe (Term.op (.inr (.mk identity)) arguments), observe (Term.var (S := signature S source) position)) ≠ none := by
  subst Δ
  subst sort
  have recognized := VariableSpines.complete (S := signature S source) _ arguments rho spine
  have noLeft := (declined_refutations _ _ (declined_refutation_equation _ _ unrefuted)).1
  obtain ⟨formal, mapped⟩ := preimage_of_unrefuted identity arguments rho recognized position noLeft
  subst position
  intro declined
  exact variable_binding_available (S := S) (source := source) identity arguments rho recognized injective formal
    (declined_bindings _ _ (declined_parts _ _ (declined_equation _ _ declined)).2.1).1

theorem object_hole_available (identity : V) {Γ Δ : Ctx S} {sort : S.Srt}
    (arguments : Args (signature S source) ((source identity).1.map fun result => ([], result)) Γ)
    (rho : Ren S (source identity).1 Γ)
    (spine : ∀ result position, argsToSub arguments result position = .var (rho result position))
    (injective : ∀ result, Function.Injective (rho result)) (position : Var Δ sort)
    (contexts : Γ = Δ) (sorts : (source identity).2 = sort)
    (unrefuted : ContextualEquationRefutation.tryEquation (observe (Term.var (S := signature S source) position),
      observe (Term.op (.inr (.mk identity)) arguments)) = none) :
    tryEquation (observe (Term.var (S := signature S source) position), observe (Term.op (.inr (.mk identity)) arguments)) ≠ none := by
  subst Δ
  subst sort
  have recognized := VariableSpines.complete (S := signature S source) _ arguments rho spine
  have noRight := (declined_refutations _ _ (declined_refutation_equation _ _ unrefuted)).2
  obtain ⟨formal, mapped⟩ := preimage_of_unrefuted identity arguments rho recognized position noRight
  subst position
  intro declined
  exact variable_binding_available (S := S) (source := source) identity arguments rho recognized injective formal
    (declined_bindings _ _ (declined_parts _ _ (declined_equation _ _ declined)).2.1).2

theorem hole_rigid_available (identity : V) {Γ Δ : Ctx S} {sort : S.Srt}
    (arguments : Args (signature S source) ((source identity).1.map fun result => ([], result)) Γ)
    (rho : Ren S (source identity).1 Γ)
    (spine : ∀ result position, argsToSub arguments result position = .var (rho result position))
    (operator : S.Op sort) (fields : Args (signature S source) (S.arity operator) Δ)
    (contexts : Γ = Δ) (sorts : (source identity).2 = sort) :
    tryEquation (observe (Term.op (.inr (.mk identity)) arguments), observe (Term.op (.inl operator) fields)) ≠ none := by
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
    (contexts : Γ = Δ) (sorts : (source identity).2 = sort) :
    tryEquation (observe (Term.op (.inl operator) fields), observe (Term.op (.inr (.mk identity)) arguments)) ≠ none := by
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
    (contexts : Γ = Δ) (sorts : (source first).2 = (source second).2) :
    tryEquation (observe (Term.op (.inr (.mk first)) arguments), observe (Term.op (.inr (.mk second)) remaining)) ≠ none := by
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
    (unrefuted : ContextualEquationRefutation.tryEquation equation = none) : tryEquation equation ≠ none := by
  have flexible := normal_has_flexible normal
  obtain ⟨contexts, sorts⟩ := normal_metadata normal
  rcases equation with ⟨left, right⟩
  have leftShape := observation_shape left first
  have rightShape := observation_shape right second
  cases leftShape with
  | object position =>
      cases rightShape with
      | object other => cases flexible
      | rigid operator fields => cases flexible
      | hole identity arguments rho spine injective =>
          exact object_hole_available identity arguments rho spine injective position contexts.symm sorts.symm unrefuted
  | rigid operator fields =>
      cases rightShape with
      | object position => cases flexible
      | rigid other remaining => cases flexible
      | hole identity arguments rho spine injective =>
          exact rigid_hole_available identity arguments rho spine operator fields contexts.symm sorts.symm
  | hole identity arguments rho spine injective =>
      cases rightShape with
      | object position => exact hole_object_available identity arguments rho spine injective position contexts sorts unrefuted
      | rigid operator fields => exact hole_rigid_available identity arguments rho spine operator fields contexts sorts
      | hole other remaining sigma otherSpine otherInjective =>
          exact holes_available identity other arguments remaining rho sigma spine otherSpine contexts sorts

theorem nonempty_normal_unrefuted_pattern_choice (problem : Problem source) (normal : ProblemNormal problem)
    (patterned : ProblemPattern problem) (unrefuted : ContextualEquationRefutation.choose problem = none)
    (nonempty : problem ≠ []) : ContextualFrameWorklist.choose problem ≠ none := by
  cases problem with
  | nil => exact False.elim (nonempty rfl)
  | cons equation rest =>
      have both := patterned equation List.mem_cons_self
      have available := equation_available (normal equation List.mem_cons_self) both.1 both.2 (head_unrefuted unrefuted)
      intro declined
      unfold ContextualFrameWorklist.choose at declined
      have noSelection := Option.map_eq_none_iff.mp declined
      simp only [ContextualSolverSelect.choose] at noSelection
      split at noSelection
      · cases noSelection
      · rename_i computed
        exact available computed

theorem normal_unrefuted_pattern_saturated_empty (problem : Problem source) (normal : ProblemNormal problem)
    (patterned : ProblemPattern problem) (unrefuted : ContextualEquationRefutation.choose problem = none)
    (saturated : ContextualFrameWorklist.choose problem = none) : problem = [] := by
  by_contra nonempty
  exact nonempty_normal_unrefuted_pattern_choice problem normal patterned unrefuted nonempty saturated

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualUnrefutedPatternAvailability
