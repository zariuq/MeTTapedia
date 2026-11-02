import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualImitationProgress
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualSumRoster
import Mettapedia.OSLF.Syntax.BindingArgumentSlotSupport
import Mettapedia.OSLF.Syntax.BindingArgumentSlotPositions

/-!
# Fresh-field imitation decreases the actual queue's active potential

Only field helpers and already active unselected declarations can appear
after imitation. The existing field-size factorization therefore bounds the
potential on the actual residual roster, rather than an assumed finite
ambient family. Bound field prefixes belong to the helpers' own interfaces.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualImitationActive

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualResidual
open ContextualImitation
open ContextualActiveSupport

variable {S : Signature} {Other Next : Type} [DecidableEq Other] {next : Next → MetaArity S}

def targetRoster {result : S.Srt} (operator : S.Op result)
    (before : Finset (Unit ⊕ Other)) : Finset (ArgumentSlots.Slot (S.arity operator) ⊕ Other) :=
  Finset.univ.disjSum before.toRight

omit [DecidableEq Other] in
theorem answer_is_bounded (parameters : Ctx S) {result : S.Srt} (operator : S.Op result)
    (others : Other → MetaArity S) (before : Finset (Unit ⊕ Other)) :
    ∀ identity ∈ before, Bounded (fun name => name ∈ targetRoster operator before)
      (answer parameters operator others identity) := by
  intro identity present
  cases identity with
  | inl marker =>
      cases marker
      change BoundedArgs (fun name => name ∈ targetRoster operator before) (freshFields parameters operator others)
      apply ArgumentSlots.bounded_tabulate
      intro field position name named
      rw [support_generator, List.mem_singleton] at named
      subst name
      exact Finset.inl_mem_disjSum.mpr (Finset.mem_univ _)
  | inr identity =>
      intro name named
      rw [answer, support_generator, List.mem_singleton] at named
      subst name
      exact Finset.inr_mem_disjSum.mpr (Finset.mem_toRight.mpr present)

theorem active_is_bounded (parameters : Ctx S) {result : S.Srt} (operator : S.Op result)
    (others : Other → MetaArity S) (problem : Problem (sourceDeclarations parameters result others)) :
    active (mapProblem (answer parameters operator others) problem) ⊆ targetRoster operator (active problem) :=
  map_active_subset _ problem (active problem) _ (fun _ member => member)
    (answer_is_bounded parameters operator others (active problem))

omit [DecidableEq Other] in
theorem roster_potential (parameters : Ctx S) {result : S.Srt} (operator : S.Op result)
    (others : Other → MetaArity S) (before : Finset (Unit ⊕ Other))
    (candidate : Assignment (targetDeclarations parameters operator others) next) :
    potential candidate (targetRoster operator before) =
      ContextualImitationProgress.targetPotential parameters operator others candidate before.toRight := by
  rw [targetRoster, ContextualSumRoster.potential_disjSum]
  rfl

theorem model_progress (parameters : Ctx S) {result : S.Srt} (operator : S.Op result)
    (others : Other → MetaArity S) {Γ : Ctx S} (rho : Ren S parameters Γ)
    (fields : Args (signature S (sourceDeclarations parameters result others)) (S.arity operator) Γ)
    (problem : Problem (sourceDeclarations parameters result others))
    (selected :
      (observe (rename (S := signature S (sourceDeclarations parameters result others)) rho
        (generator (sourceDeclarations parameters result others) (.inl ()))),
       observe (Term.op (.inl operator) fields)) ∈ problem)
    (candidate : Assignment (sourceDeclarations parameters result others) next) (solved : Models candidate problem) :
    ∃ remaining : Assignment (targetDeclarations parameters operator others) next,
      Models remaining (mapProblem (answer parameters operator others) problem) ∧
      (∀ identity, candidate identity = instantiate remaining (answer parameters operator others identity)) ∧
      potential remaining (active (mapProblem (answer parameters operator others) problem)) <
        potential candidate (active problem) := by
  obtain ⟨remaining, models, components, decrease⟩ := ContextualImitationProgress.model_progress
    parameters operator others rho fields problem selected candidate solved (active problem).toRight
  have root : .inl () ∈ active problem := by
    apply (mem_active _ _).mpr
    refine ⟨_, selected, .inl ?_⟩
    change .inl () ∈ support (rename (S := signature S (sourceDeclarations parameters result others)) rho
      (generator (sourceDeclarations parameters result others) (.inl ())))
    rw [support_rename, support_generator]
    exact List.mem_singleton_self _
  have start := (ContextualSumRoster.unit_potential candidate (active problem) root).symm
  have finish := potential_monotone remaining (active_is_bounded parameters operator others problem)
  rw [roster_potential] at finish
  change ContextualImitationProgress.sourcePotential parameters result others candidate (active problem).toRight =
    potential candidate (active problem) at start
  exact ⟨remaining, models, components, lt_of_le_of_lt finish (start ▸ decrease)⟩

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualImitationActive
