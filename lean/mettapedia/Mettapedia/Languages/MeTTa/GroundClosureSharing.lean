import Mettapedia.Languages.MeTTa.SubstitutionAlgebra

/-!
# Ground closures may be bound in their ground form

A contextual value is a closure: a template together with the substitution
that interprets its variables.  When every variable of the template is bound
to ground syntax, one substitution step already yields a ground term
(`vars_subst_eq_nil_of_ground`).  That instance is the closure's meaning for
good:

* any later substitution extending the current one gives the template the
  same instance (`ground_instance_stable`) — bindings are only added along a
  branch, and rollback removes a binding before anything it depended on;
* further resolution leaves it unchanged (`ground_instance_resolved`), so the
  one-step instance is also the fully resolved, triangular meaning.

Binding a fresh slot to the ground instance instead of the closure is
therefore invisible to every observer, and it replaces a resolution chain
that grows with the closure's history by a single shared atom.

The side conditions are necessary.  A template with an unbound variable, or
with a variable bound to syntax that is itself open, has an instance that a
later binding changes (`unbound_variable_changes_instance`,
`open_binding_changes_resolution`).  CeTTa's ground-on-bind declines when a
variable's root is unbound or not ground syntax; its bounded traversal may
also decline when the node budget or allocation capacity is exhausted.

CeTTa realizes this at the exclusive frame's local-slot write in `src/match.c`
(`binding_value_ground_or_self`).  Relating the C resolver to `subst`, and the
arena lifetime of the built atom to rollback order, remain realization
obligations.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.GroundClosureSharing

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.SubstitutionAlgebra
  (Var Subst vars subst subst_congr_on_vars subst_of_vars_eq_nil)

/-- Every variable of the template is bound to ground syntax. -/
def GroundBound (σ : Subst) (t : Atom) : Prop :=
  ∀ v ∈ vars t, ∃ g, σ v = some g ∧ vars g = []

/-- `τ` keeps every binding of `σ`. -/
def Extends (τ σ : Subst) : Prop :=
  ∀ v g, σ v = some g → τ v = some g

theorem varsList_substList_eq_nil (σ : Subst) (as : List Atom)
    (ih : ∀ a ∈ as, GroundBound σ a → vars (subst σ a) = [])
    (ground : ∀ v ∈ vars.varsList as, ∃ g, σ v = some g ∧ vars g = []) :
    vars.varsList (subst.substList σ as) = [] := by
  induction as with
  | nil => rfl
  | cons a as ihs =>
      simp only [subst.substList, vars.varsList]
      have head : GroundBound σ a := fun v member =>
        ground v (by simp [vars.varsList, member])
      have tail : ∀ v ∈ vars.varsList as, ∃ g, σ v = some g ∧ vars g = [] :=
        fun v member => ground v (by simp [vars.varsList, member])
      rw [ih a (List.mem_cons_self ..) head,
        ihs (fun b member => ih b (List.mem_cons_of_mem a member)) tail]
      rfl

/-- One step of substitution grounds a template whose variables are all
bound to ground syntax. -/
theorem vars_subst_eq_nil_of_ground (σ : Subst) (t : Atom)
    (ground : GroundBound σ t) : vars (subst σ t) = [] := by
  match t with
  | .symbol _ => rfl
  | .grounded _ => rfl
  | .var v =>
      obtain ⟨g, bound, groundValue⟩ := ground v (by simp [vars])
      simp [subst, bound, groundValue]
  | .expression es =>
      simp only [subst, vars]
      exact varsList_substList_eq_nil σ es
        (fun b _ member => vars_subst_eq_nil_of_ground σ b member)
        (by simpa [GroundBound, vars] using ground)
termination_by sizeOf t

/-- The instance does not change under any extension of the substitution. -/
theorem ground_instance_stable {σ τ : Subst} (grows : Extends τ σ)
    (t : Atom) (ground : GroundBound σ t) : subst τ t = subst σ t :=
  subst_congr_on_vars τ σ t fun v member => by
    obtain ⟨g, bound, _⟩ := ground v member
    rw [grows v g bound, bound]

/-- Resolving the instance further, by any substitution, leaves it fixed: the
one-step instance is the fully resolved meaning. -/
theorem ground_instance_resolved (σ ρ : Subst) (t : Atom)
    (ground : GroundBound σ t) : subst ρ (subst σ t) = subst σ t :=
  subst_of_vars_eq_nil ρ (subst σ t) (vars_subst_eq_nil_of_ground σ t ground)

/-- An extension keeps the template ground-bound, so the property that
licensed the ground form survives every later binding on the branch. -/
theorem groundBound_extends {σ τ : Subst} (grows : Extends τ σ)
    {t : Atom} (ground : GroundBound σ t) : GroundBound τ t := by
  intro v member
  obtain ⟨g, bound, groundValue⟩ := ground v member
  exact ⟨g, grows v g bound, groundValue⟩

/-! ## The side conditions are necessary -/

private def template : Atom := .expression [.symbol "f", .var "v"]

private def bindV (value : Atom) : Subst :=
  fun x => if x = "v" then some value else none

/-- With `v` unbound the one-step instance is `(f v)`; binding `v` later
changes the closure's meaning to `(f a)`. -/
theorem unbound_variable_changes_instance :
    ¬ GroundBound (fun _ => none) template ∧
      subst (bindV (.symbol "a")) template ≠
        subst (fun _ => none) template := by
  refine ⟨?_, ?_⟩
  · intro ground
    obtain ⟨_, bound, _⟩ := ground "v" (by decide)
    cases bound
  · decide

/-- With `v` bound to the open `(g w)`, a later binding of `w` changes the
resolved meaning, so an instance built early would be stale. -/
theorem open_binding_changes_resolution :
    let σ : Subst := bindV (.expression [.symbol "g", .var "w"])
    let τ : Subst := fun x =>
      if x = "v" then some (.expression [.symbol "g", .var "w"])
      else if x = "w" then some (.symbol "a") else none
    ¬ GroundBound σ template ∧ Extends τ σ ∧
      subst τ (subst τ template) ≠ subst σ template := by
  refine ⟨?_, ?_, ?_⟩
  · intro ground
    obtain ⟨_, bound, groundValue⟩ := ground "v" (by decide)
    simp [bindV] at bound
    subst bound
    simp [vars, vars.varsList] at groundValue
  · intro x g bound
    by_cases same : x = "v"
    · subst same
      simpa [bindV] using bound
    · simp [bindV, same] at bound
  · decide

/-- Positive control: `v` bound to the ground `(g a)` makes `(f v)` ground,
and binding more variables later leaves its instance unchanged. -/
theorem ground_template_is_stable :
    let σ : Subst := bindV (.expression [.symbol "g", .symbol "a"])
    let τ : Subst := fun x =>
      if x = "v" then some (.expression [.symbol "g", .symbol "a"])
      else if x = "w" then some (.symbol "b") else none
    GroundBound σ template ∧ subst τ template = subst σ template ∧
      vars (subst σ template) = [] := by
  intro σ τ
  have ground : GroundBound σ template := by
    intro v member
    simp [template, vars, vars.varsList] at member
    subst member
    exact ⟨.expression [.symbol "g", .symbol "a"], by simp [σ, bindV], by decide⟩
  have grows : Extends τ σ := by
    intro x g bound
    by_cases same : x = "v"
    · subst same
      simpa [σ, τ, bindV] using bound
    · simp [σ, bindV, same] at bound
  exact ⟨ground, ground_instance_stable grows template ground,
    vars_subst_eq_nil_of_ground σ template ground⟩

end Mettapedia.Languages.MeTTa.GroundClosureSharing
