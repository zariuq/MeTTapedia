import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualPatternBinding
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualResidual

/-!
# Recoverable contextual bindings retain all future-frame solutions

A successful common strengthening and occurs check gives a principal answer
in every later declaration family. The selected equation can therefore leave
the worklist while its substitution acts on all retained equations. No
failure of this particular binding case is classified as inconsistency.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualBindingReduction

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily

variable {S : Signature} {V : Type} [DecidableEq V] {declaration : V → MetaArity S}

def inFamily {Next : Type} (next : Next → MetaArity S) (identity : V) {Γ : Ctx S}
    {rho : Ren S (declaration identity).1 Γ}
    (inverse : Strengthener (S := signature S declaration) rho) :
    Strengthener (S := signature S next) rho where
  un := inverse.un
  un_rho := inverse.un_rho
  rho_un := inverse.rho_un

theorem principal (identity : V) {Γ : Ctx S} (rho : Ren S (declaration identity).1 Γ)
    (inverse : Strengthener (S := signature S declaration) rho)
    (target : Term (signature S declaration) Γ (declaration identity).2)
    (answer : Assignment declaration declaration)
    (computed : ContextualPatternBinding.solve? identity rho inverse target = some answer) :
    ContextualFrameUnifier.Principal
      [(rename (S := signature S declaration) rho (generator declaration identity), target)] answer := by
  obtain ⟨body, recovered, absent, rfl⟩ :=
    (ContextualPatternBinding.solve_success_iff identity rho inverse target answer).mp computed
  rw [← recovered]
  constructor
  · intro equation member
    have only := List.mem_singleton.mp member
    subst equation
    change instantiate (ContextualBinding.answer identity body)
      (rename (S := signature S declaration) rho (generator declaration identity)) =
      instantiate (ContextualBinding.answer identity body) (rename (S := signature S declaration) rho body)
    rw [ContextualFamily.instantiate_rename, ContextualFamily.instantiate_rename, instantiate_generator,
      ContextualBinding.answer_same, ContextualBinding.instantiate_answer_of_absent identity body body absent]
  · intro Next next candidate solved
    have same := solved _ (List.mem_singleton_self _)
    change instantiate candidate (rename (S := signature S declaration) rho (generator declaration identity)) =
      instantiate candidate (rename (S := signature S declaration) rho body) at same
    rw [ContextualFamily.instantiate_rename, ContextualFamily.instantiate_rename, instantiate_generator] at same
    have binding := rename_injective (inFamily next identity inverse) same
    have components := ContextualBinding.candidate_factors identity body candidate binding
    exact ⟨candidate, fun other => congrFun components other⟩

theorem reduction (identity : V) {Γ : Ctx S} (rho : Ren S (declaration identity).1 Γ)
    (inverse : Strengthener (S := signature S declaration) rho)
    (target : Term (signature S declaration) Γ (declaration identity).2)
    (answer : Assignment declaration declaration)
    (computed : ContextualPatternBinding.solve? identity rho inverse target = some answer)
    (remaining : ContextualResidual.Problem declaration) :
    ContextualResidual.Reduction
      ((observe (rename (S := signature S declaration) rho (generator declaration identity)), observe target) :: remaining)
      answer (ContextualResidual.mapProblem answer remaining) :=
  ContextualResidual.of_principal_prefix (principal identity rho inverse target answer computed) remaining

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualBindingReduction
