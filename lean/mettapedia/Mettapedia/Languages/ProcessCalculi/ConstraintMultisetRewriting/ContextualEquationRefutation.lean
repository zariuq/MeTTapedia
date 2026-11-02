import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualPatternOccurs
import Mettapedia.OSLF.Syntax.BindingRenamingInverse
import Mettapedia.OSLF.Syntax.BindingVariableSpineApplications

/-!
# Certified scope and finite-pattern occurs refusals on contextual equations

A variable outside a hole's argument image cannot be supplied by that hole.
A rigid structural pattern containing the hole is strictly larger than its
image under every finite assignment. These are refutations over all later
declaration frames. Failed recovery of other applications stays unresolved;
in particular a flexible application may erase an argument.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualEquationRefutation

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualResidual

variable {S : Signature} {V : Type} [DecidableEq V] [DecidableEq S.Srt]
  {source : V → MetaArity S}

abbrev Refutes (problem : Problem source) : Prop :=
  ∀ {Next : Type} (next : Next → MetaArity S) (candidate : Assignment source next),
    ¬ Models candidate problem

abbrev RefutesTerms {Γ : Ctx S} {sort : S.Srt}
    (left right : Term (signature S source) Γ sort) : Prop :=
  ∀ {Next : Type} (next : Next → MetaArity S) (candidate : Assignment source next),
    instantiate candidate left ≠ instantiate candidate right

structure Refutation (problem : Problem source) : Type where
  noModel : Refutes problem

structure TermRefutation {Γ : Ctx S} {sort : S.Srt}
    (left right : Term (signature S source) Γ sort) : Type where
  noEqual : RefutesTerms left right

omit [DecidableEq V] [DecidableEq S.Srt] in
theorem variable_outside_image {T : Signature}
    {parameters Γ : Ctx T} (rho : Ren T parameters Γ) {sort : T.Srt}
    (position : Var Γ sort) (missing : ∀ formal, rho sort formal ≠ position)
    (body : Term T parameters sort) :
    rename (S := T) rho body ≠ .var position := by
  intro same
  cases body with
  | var formal =>
      have mapped : rho sort formal = position := Term.var.inj same
      exact missing formal mapped
  | op operator arguments => cases same

def tryLeft : {Γ : Ctx S} → {sort : S.Srt} →
    (left right : Term (signature S source) Γ sort) → Option (TermRefutation left right)
  | _, _, .op (.inr (.mk identity)) arguments, target => by
      exact match recognized : VariableSpines.recognize (S := signature S source)
          (source identity).1 arguments with
      | none => none
      | some rho => by
          cases target with
          | var position =>
              by_cases missing : RenamingInverse.inverse rho _ position = none
              · refine some ⟨?_⟩
                intro Next next candidate same
                rw [VariableSpines.application_eq_rename_generator identity arguments rho
                  (VariableSpines.sound _ arguments rho recognized),
                  ContextualFamily.instantiate_rename, instantiate_generator] at same
                apply variable_outside_image (T := signature S next) rho position ?_ (candidate identity) same
                intro formal mapped
                have excluded := List.find?_eq_none.mp missing formal
                  (RenamingInverse.ofSort_complete (S := signature S source) _ _ formal)
                simp [mapped] at excluded
              · exact none
          | op operator fields =>
              cases operator with
              | inr _ => exact none
              | inl operator =>
                  by_cases structural : ContextualPatternFragment.checkArgs fields = true
                  · by_cases present : identity ∈ supportArgs fields
                    · refine some ⟨?_⟩
                      intro Next next candidate
                      rw [VariableSpines.application_eq_rename_generator identity arguments rho
                        (VariableSpines.sound _ arguments rho recognized)]
                      exact ContextualPatternOccurs.no_finite_solution candidate identity rho operator fields
                        (ContextualPatternFragment.checkArgs_sound fields structural) present
                    · exact none
                  · exact none
  | _, _, _, _ => none

def tryTerms {Γ : Ctx S} {sort : S.Srt} (left right : Term (signature S source) Γ sort) :
    Option (TermRefutation left right) :=
  (tryLeft left right).orElse fun _ => (tryLeft right left).map fun reversed =>
    ⟨fun next candidate same => reversed.noEqual next candidate same.symm⟩

def tryEquation (equation : Equation (Observation S source)) : Option (Refutation [equation]) := by
  rcases equation with ⟨⟨Γ, sort, left⟩, ⟨Δ, result, right⟩⟩
  by_cases contexts : Γ = Δ
  · subst Δ
    by_cases sorts : sort = result
    · subst result
      exact (tryTerms left right).map fun refused => ⟨fun next candidate solved =>
        refused.noEqual next candidate (observe_injective (solved _ (List.mem_singleton_self _)))⟩
    · exact none
  · exact none

def choose : (problem : Problem source) → Option (Refutation problem)
  | [] => none
  | equation :: rest =>
      match tryEquation equation with
      | some refused => some ⟨fun next candidate solved =>
          refused.noModel next candidate fun pair member => by
            have same := List.mem_singleton.mp member
            subst pair
            exact solved equation List.mem_cons_self⟩
      | none => (choose rest).map fun refused => ⟨fun next candidate solved =>
          refused.noModel next candidate fun pair member => solved pair (List.mem_cons_of_mem equation member)⟩

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualEquationRefutation
