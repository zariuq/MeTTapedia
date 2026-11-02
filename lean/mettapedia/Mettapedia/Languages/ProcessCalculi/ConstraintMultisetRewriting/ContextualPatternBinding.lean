import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualBinding
import Mettapedia.OSLF.Syntax.PartialRenaming

/-!
# Principal binding along distinct-variable contextual spines

The existing strengthening algorithm recovers a body from the image of an
injective, sort-preserving parameter renaming. Combining it with contextual
binding gives a principal answer even when that body contains unresolved
metavariables. Reordered parameters are permitted; repeated parameters do
not have a partial inverse and require different solver cases.

The exact success fragment is a structurally recoverable body without the
hole being bound. Failure of recovery is not global unification failure:
other flexible holes can lose dependencies when further instantiated.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualPatternBinding

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily

variable {S : Signature} {V : Type} [DecidableEq V]
  {declaration : V → MetaArity S}

omit [DecidableEq V] in
theorem solves_on_spine_iff (identity : V) {Γ : Ctx S}
    (rho : Ren S (declaration identity).1 Γ)
    (inverse : Strengthener (S := signature S declaration) rho)
    (body : Term (signature S declaration) (declaration identity).1 (declaration identity).2)
    (candidate : Assignment declaration declaration) :
    (ContextualFamilies.action declaration Γ (declaration identity).2).Solves candidate
        (rename (S := signature S declaration) rho (generator declaration identity),
          rename (S := signature S declaration) rho body) ↔
      candidate identity = instantiate candidate body := by
  change instantiate candidate (rename (S := signature S declaration) rho (generator declaration identity)) =
    instantiate candidate (rename (S := signature S declaration) rho body) ↔ _
  rw [ContextualFamily.instantiate_rename, ContextualFamily.instantiate_rename, instantiate_generator]
  exact ⟨rename_injective inverse, congrArg (rename (S := signature S declaration) rho)⟩

theorem principal_on_spine (identity : V) {Γ : Ctx S}
    (rho : Ren S (declaration identity).1 Γ)
    (inverse : Strengthener (S := signature S declaration) rho)
    (body : Term (signature S declaration) (declaration identity).1 (declaration identity).2)
    (absent : identity ∉ support body) :
    (ContextualFamilies.action declaration Γ (declaration identity).2).Principal
      [(rename (S := signature S declaration) rho (generator declaration identity),
        rename (S := signature S declaration) rho body)] (ContextualBinding.answer identity body) := by
  constructor
  · intro equation member
    have same := List.mem_singleton.mp member
    subst equation
    apply (solves_on_spine_iff identity rho inverse body _).mpr
    rw [ContextualBinding.answer_same, ContextualBinding.instantiate_answer_of_absent identity body body absent]
  · intro candidate solved
    have binding := solved
      (rename (S := signature S declaration) rho (generator declaration identity),
        rename (S := signature S declaration) rho body) (by simp)
    have components := ContextualBinding.candidate_factors identity body candidate
      ((solves_on_spine_iff identity rho inverse body candidate).mp binding)
    exact ⟨candidate, fun term => congrArg (fun assignment => instantiate assignment term) components⟩

def solve? (identity : V) {Γ : Ctx S} (rho : Ren S (declaration identity).1 Γ)
    (inverse : Strengthener (S := signature S declaration) rho)
    (target : Term (signature S declaration) Γ (declaration identity).2) :
    Option (Assignment declaration declaration) := do
  let body ← strengthenT inverse target
  ContextualBinding.solve? identity body

/-- Soundness and completeness of this executable binding case for its
declared structural fragment. No negative verdict is assigned outside it. -/
theorem solve_success_iff (identity : V) {Γ : Ctx S}
    (rho : Ren S (declaration identity).1 Γ)
    (inverse : Strengthener (S := signature S declaration) rho)
    (target : Term (signature S declaration) Γ (declaration identity).2)
    (assignment : Assignment declaration declaration) :
    solve? identity rho inverse target = some assignment ↔
      ∃ body, rename (S := signature S declaration) rho body = target ∧
        identity ∉ support body ∧ ContextualBinding.answer identity body = assignment := by
  simp only [solve?, Option.bind_eq_bind, Option.bind_eq_some_iff]
  constructor
  · rintro ⟨body, recovered, bound⟩
    unfold ContextualBinding.solve? at bound
    split at bound
    · cases bound
    · exact ⟨body, (strengthenT_eq_some_iff inverse target body).mp recovered,
        by assumption, Option.some.inj bound⟩
  · rintro ⟨body, recovered, absent, rfl⟩
    exact ⟨body, (strengthenT_eq_some_iff inverse target body).mpr recovered,
      by simp [ContextualBinding.solve?, absent]⟩

theorem solve_principal (identity : V) {Γ : Ctx S}
    (rho : Ren S (declaration identity).1 Γ)
    (inverse : Strengthener (S := signature S declaration) rho)
    (target : Term (signature S declaration) Γ (declaration identity).2)
    {assignment : Assignment declaration declaration}
    (success : solve? identity rho inverse target = some assignment) :
    (ContextualFamilies.action declaration Γ (declaration identity).2).Principal
      [(rename (S := signature S declaration) rho (generator declaration identity), target)] assignment := by
  obtain ⟨body, recovered, absent, rfl⟩ := (solve_success_iff identity rho inverse target assignment).mp success
  rw [← recovered]
  exact principal_on_spine identity rho inverse body absent

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualPatternBinding
