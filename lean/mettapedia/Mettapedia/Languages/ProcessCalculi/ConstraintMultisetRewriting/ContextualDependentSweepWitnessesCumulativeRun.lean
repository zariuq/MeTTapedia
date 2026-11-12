import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentSweepWitnessesCumulative

/-!
# Stuck stores where a local of a smaller universe is passed to an unknown declared at a larger one: the runs

The statements of this module reduce the runs of the top family on `crossStore` and `fixedStore` to the readings of
its compiled run, which is the ending of the family's run at every budget and number of rounds
(`ContextualDependentSweep.endingSort_run`). The compiled run reads `stuck` on both stores at budgets 16 and 64;
those readings are evaluations. The two runs evaluated by the kernel in one module exceed the memory of the check.
The run on `fixedStore`, alone in a module, is a kernel statement
(`ContextualDependentSweepWitnessesCumulativeFixedRun`); the run on `crossStore` alone exceeds the memory too, and
no kernel statement of it is made.

* `fixed_gap_of_ending`: `fixedStore` is in the fragment, has no solution, and the top family is stuck on it
  wherever its compiled run reads `stuck`: a refutation is missing.
* `cross_two_answers`: `crossStore` is in the fragment, and two substitutions that send `Y` to different codes
  both solve it (`cross_answers_differ`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentSweep.Witnesses

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentWorklist ContextualDependentDynamicFragment
open ContextualDependentPatternFiring.Controls ContextualDependentAcceptance4
open ContextualDependentEtaDepth ContextualDependentEtaDepth.Controls ContextualDependentEtaDepth.ArgControls
open ContextualDependentEtaDepth.BaseControls

/-- **A store of the fragment without solution on which the top family is stuck** wherever its compiled run reads
`stuck`. -/
theorem fixed_gap_of_ending {fuel rounds : Nat} (read : endingSort fuel rounds ctxMixed fixedStore = .stuck) :
    InFragmentStore fixedStore ∧ ¬ (frames setting.levels).Solvable fixedStore ∧
      isStuck (run (sortTower.solver fuel) fixedStore rounds) = true :=
  ⟨fixed_in_fragment, fixed_unsolvable, stuck_of_endingSort read⟩

/-- A substitution solves a one-equation store as soon as the executable conversion accepts its instantiated
sides. -/
theorem models_by {Γ Δ : Context setting.R} (σ : Δ ⟶ Γ) {type : TypeOver Γ} (left right : Term Γ type)
    (accepted : (ExecutableConversion.compare setting.R (ContextualDependentExecutableConversion.red (L := Nat)) 64
      Δ.raw (subst σ.substitution left.code) (subst σ.substitution right.code)
      (subst σ.substitution type.code)).isSome = true) :
    (frames setting.levels).Models σ [((⟨type, left⟩ : TotalTerm Γ), (⟨type, right⟩ : TotalTerm Γ))] := by
  refine (models_iff setting.levels σ _).mpr ?_
  intro equation member
  rw [List.mem_singleton.mp member]
  refine ⟨(type.reindex σ).isType.refl, ?_⟩
  cases computed : ExecutableConversion.compare setting.R (ContextualDependentExecutableConversion.red (L := Nat)) 64
      Δ.raw (subst σ.substitution left.code) (subst σ.substitution right.code)
      (subst σ.substitution type.code) with
  | none =>
      rw [computed] at accepted
      cases accepted
  | some found =>
      exact Algorithm.sound (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
        found.down Δ.formed (left.reindex σ).typed (right.reindex σ).typed

/-- **A store of the fragment solved by the identities and by the constant families.** -/
theorem cross_two_answers : InFragmentStore crossStore ∧
    (frames setting.levels).Models crossIdentity crossStore ∧
    (frames setting.levels).Models crossConstant crossStore :=
  ⟨cross_in_fragment, models_by crossIdentity crossEquation.1.2 crossEquation.2.2 (by decide +kernel),
    models_by crossConstant crossEquation.1.2 crossEquation.2.2 (by decide +kernel)⟩

/-- The two answers send `Y` to different codes: the identity and the constant family at the ground type. -/
theorem cross_answers_differ :
    crossIdentity.substitution (⟨0, Nat.zero_lt_two⟩ : Fin 2) ≠
      crossConstant.substitution (⟨0, Nat.zero_lt_two⟩ : Fin 2) := by decide +kernel

end ContextualDependentSweep.Witnesses
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
