import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.ScopedComputationPreservation
import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.ScopedComputationExamples

/-!
# Qualified native operations throughout scoped computations

The independently authored state-marking and reflexivity operations satisfy
the general primitive result contract. Consequently every independently typed
program over these operations preserves native admission, including after a
refined substitution into a different formed context. This is not limited to
the concrete selected-index example.

An altered reflexivity implementation can agree exactly with its own altered
world semantics while failing the declared result family. The negative control
separates operational realization from logical qualification.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.Presentation
namespace ScopedComputation.NativeExamples

open Mettapedia.GSLT.Dynamics.ContextualEffectHandlers

variable {n m : Nat} {Γ : Tower.Ctx n} {Δ : Tower.Ctx m}

/-- The result contract is discharged against the actual native operation
implementation for every admitted argument, not assumed for the specimen. -/
theorem primitive_preserves : PrimitivePreserves Tower.rules signature Γ primitiveWorlds := by
  intro operation argument state branch output _ admitted returned
  exact primitive_world_typing operation argument state branch output admitted returned

/-- Every admitted source computation over these three operations has
admitted results under every refined environment into a formed context. -/
theorem admitted_program_results {code : Code Tower.Head Operation n} {A : Tower.Tm n}
    (judgment : Judgment Tower.rules signature Γ code A)
    {environment : Sub Tower.Head n m}
    (target : FormationSensitive.ContextFormation Tower.rules Δ)
    (typed : FormationSensitive.CtxMor Tower.rules Γ Δ environment)
    {state : Bool} {branch : BranchTrace} {output : WorldResult Bool (Tower.Tm m) Nat}
    (returned : output ∈ runWorldsAt (Code.interpret handler environment code) state branch) :
    FormationSensitive.Judgment Tower.rules Δ output.answer (subst environment A) :=
  judgment.interpret_preserve handler primitiveWorlds handler_realizes target typed
    primitive_preserves returned

/-- The effectfully selected dependent source retains native admission after
an arbitrary refined substitution. Its selected value remains in the Sigma. -/
theorem substituted_source_results {environment : Sub Tower.Head 2 m}
    (target : FormationSensitive.ContextFormation Tower.rules Δ)
    (typed : FormationSensitive.CtxMor Tower.rules context Δ environment)
    {state : Bool} {branch : BranchTrace} {output : WorldResult Bool (Tower.Tm m) Nat}
    (returned : output ∈ runWorldsAt (Code.interpret handler environment source) state branch) :
    FormationSensitive.Judgment Tower.rules Δ output.answer
      (subst environment (.sigma ground identityFamily)) :=
  admitted_program_results source_judgment target typed returned

theorem source_results {state : Bool} {branch : BranchTrace}
    {output : WorldResult Bool (Tower.Tm 2) Nat}
    (returned : output ∈ runWorldsAt (Code.interpret handler ids source) state branch) :
    FormationSensitive.Judgment Tower.rules context output.answer
      (.sigma ground identityFamily) := by
  have typed : FormationSensitive.CtxMor Tower.rules context context ids := by
    intro index
    simpa only [ids, subst_ids] using
      (FormationSensitive.Typing.var (R := Tower.rules) (Γ := context) index)
  simpa only [subst_ids] using substituted_source_results context_formed typed returned

/-- This implementation ignores reflexivity's actual argument and returns
the older variable's reflexivity instead. The other effects are unchanged. -/
def misindexedHandler : Operation → Tower.Tm 2 → Program Bool (Tower.Tm 2) Nat
  | .reflexivity, _ =>
      .read fun state => .intent (if state then 30 else 40) (.pure (.refl older))
  | .markTrue, argument => handler .markTrue argument
  | .markFalse, argument => handler .markFalse argument

/-- A correspondingly altered operational specification, independently
authored without calling the handler interpreter. -/
def misindexedWorlds : Operation → Tower.Tm 2 → Bool → BranchTrace →
    List (WorldResult Bool (Tower.Tm 2) Nat)
  | .reflexivity, _, state, branch =>
      [{ branch := branch, answer := .refl older, state := state,
         intents := [if state then 30 else 40] }]
  | .markTrue, argument, state, branch => primitiveWorlds .markTrue argument state branch
  | .markFalse, argument, state, branch => primitiveWorlds .markFalse argument state branch

theorem misindexedHandler_realizes (operation : Operation) (argument : Tower.Tm 2)
    (state : Bool) (branch : BranchTrace) :
    runWorldsAt (misindexedHandler operation argument) state branch =
      misindexedWorlds operation argument state branch := by
  cases operation <;> rfl

/-- Exact realization of an operational specification cannot substitute for
the separate theorem that the declared dependent family is respected. -/
theorem misindexedWorlds_not_qualified :
    ¬ PrimitivePreserves Tower.rules signature context misindexedWorlds := by
  intro sound
  have returned :
      ({ branch := [], answer := .refl older, state := false, intents := [40] } :
        WorldResult Bool (Tower.Tm 2) Nat) ∈
      misindexedWorlds .reflexivity newer false [] := by
    exact List.mem_singleton_self _
  exact wrong_selected_index_not_admitted
    (sound .reflexivity newer false [] _ (operation_formation .reflexivity)
      (FormationSensitive.Typing.var 0) returned)

#print axioms primitive_preserves
#print axioms admitted_program_results
#print axioms substituted_source_results
#print axioms source_results
#print axioms misindexedHandler_realizes
#print axioms misindexedWorlds_not_qualified

end ScopedComputation.NativeExamples
end Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.Presentation
