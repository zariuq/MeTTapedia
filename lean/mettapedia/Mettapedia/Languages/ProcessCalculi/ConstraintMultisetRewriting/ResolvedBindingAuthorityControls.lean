import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ResolvedBindingAuthority

/-!
# Compound dependencies and the full-resolution boundary

A triangular binding table exposes only one layer per application. Its first
layer can pass a protection check while its fully resolved value changes.
The idempotent interpretation exposes the missing dependency. The contextual
control separately shows why support fixation is not necessary for preserving
one specialized higher-order observation.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ResolvedBindingAuthority.Controls

open Mettapedia.Logic.LP

abbrev signature := ConstraintMultisetRewriting.Controls.signature
abbrev f := ConstraintMultisetRewriting.Controls.f

def protectedRoots (name : Nat) : Prop := name = 0 ∨ name = 1

def triangular : Subst signature := fun name =>
  if name = 0 then f (.var 1) else if name = 1 then f (.var 2) else .var name

def resolved : Subst signature := fun name =>
  if name = 0 then f (f (.var 2)) else if name = 1 then f (.var 2) else .var name

def later : Subst signature := Subst.single 2 (.const 7)

theorem later_fixes_both_protected_roots : RigidUnification.Fixes protectedRoots later := by
  intro name isProtected
  rcases isProtected with rfl | rfl <;> rfl

theorem shallow_support_accepts : Protects (fun name : Nat => name = 0) triangular later := by
  intro root isProtected name member
  subst root
  have same : name = 1 := by
    simpa [triangular, Subst.applyTerm, Term.freeVars, f,
      ConstraintMultisetRewriting.Controls.f] using member
  subst name
  rfl

def twice (assignment : Subst signature) (term : Term signature) : Term signature :=
  assignment.applyTerm (assignment.applyTerm term)

theorem full_resolution_changes :
    twice triangular (.var 0) = f (f (.var 2)) ∧
      twice (later.comp triangular) (.var 0) = f (f (.const 7)) := ⟨rfl, rfl⟩

theorem resolved_is_idempotent : resolved.Absorbs resolved := by
  intro name
  by_cases zero : name = 0
  · subst name; rfl
  · by_cases one : name = 1
    · subst name; rfl
    · simp [resolved, zero, one]

theorem resolved_support_rejects : ¬ Protects (fun name : Nat => name = 0) resolved later := by
  intro authorized
  have wrong := authorized 0 rfl 2 (by
    simp [resolved, Subst.applyTerm, Term.freeVars, f, ConstraintMultisetRewriting.Controls.f])
  cases wrong

def equations : EquationStore (Term signature) :=
  [(.var 0, f (.var 1)), (.var 1, f (.var 2))]

theorem raw_table_is_not_a_model : ¬ (FirstOrder.action signature).Models triangular equations := by
  intro models
  have wrong := models (.var 0, f (.var 1)) (by simp [equations])
  change f (.var 1) = f (f (.var 2)) at wrong
  have inner := congrFun (eq_of_heq (Term.app.inj wrong).2) ⟨0, by decide⟩
  cases inner

theorem resolved_is_a_model : (FirstOrder.action signature).Models resolved equations := by
  intro equation member
  simp only [equations, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl <;> rfl

def harmless : Subst signature := Subst.single 3 (.const 9)

theorem a_nonidentity_extension_is_authorized : Protects (fun name : Nat => name = 0) resolved harmless := by
  intro root isProtected name member
  subst root
  have same : name = 2 := by
    simpa [resolved, Subst.applyTerm, Term.freeVars, f, ConstraintMultisetRewriting.Controls.f] using member
  subst name
  rfl

theorem authorized_extension_keeps_the_compound :
    (harmless.comp resolved).applyTerm (.var 0) = f (f (.var 2)) :=
  a_nonidentity_extension_is_authorized.preserves 0 rfl

theorem harmless_is_nonidentity : harmless 3 ≠ .var 3 := by
  intro same
  cases same

namespace Contextual

set_option backward.isDefEq.respectTransparency.types false

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualSelectionViews.Controls (base atom)
open BindingAuthority.ContextualControls (spineDeclarations)

def observed : Term (ContextualFamily.signature base spineDeclarations) [] () :=
  .op (.inr (.mk 0)) (.cons (atom spineDeclarations) .nil)

def specialized : Assignment spineDeclarations spineDeclarations
  | 0 => .op (S := ContextualFamily.signature base spineDeclarations) (Γ := [()]) (.inr (.mk 0))
      (.cons (.op (S := ContextualFamily.signature base spineDeclarations) (Γ := [()]) (.inl .constant) .nil) .nil)
  | name + 1 => generator spineDeclarations (name + 1)

theorem specialized_observation_is_unchanged : instantiate specialized observed = observed := by
  with_unfolding_all rfl

theorem specialized_metavariable_is_not_fixed : specialized 0 ≠ generator spineDeclarations 0 := by
  intro same
  have args := eq_of_heq (Term.op.inj same).2
  have first := (Args.cons.inj args).1
  cases first

end Contextual

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ResolvedBindingAuthority.Controls
