import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentPiSpineScopes
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentScopedDispatch

/-!
# Solver results for equations under supplied dependent Pi spines

The spine's actual whole annotation closes its body equation. The proved
pointwise scope law supplies the existing Closed/Result interface, so the
ordinary typed dispatcher factors solutions of the original rigid scopes.
No new universe join is chosen during this closing operation.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentPiSpineSolver

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentUpdate ContextualDependentScope ContextualDependentPiSpine

variable {Head L : Type} [UniverseLevel.LevelOrder L] {rules : Rules Head}

def closed (levels : LevelModel rules L) {Γ : Context rules} {type : TypeOver Γ} (spine : Spine type)
    (first second : Term spine.target spine.result) :
    ContextualDependentScopedDispatch.Closed levels [spine.toScoped ⟨spine.result, first, second⟩] where
  equations := [(spine.closeBody first second).equation]
  models := by
    intro Δ solution
    constructor
    · intro modeled constraint member
      obtain rfl := List.mem_singleton.mp member
      exact (spine.closed_models_iff levels first second solution).mp modeled
    · intro held
      exact (spine.closed_models_iff levels first second solution).mpr (held _ (List.mem_singleton_self _))

variable {S : Setting Head L}
variable [DecidableEq Head] [DecidableRel S.R.headEq]
  [∀ head, Decidable (S.R.isUniverse head)] [DecidableRel S.R.cumulative]
variable (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R)
  (heads : HeadPreserving S.R) (algebra : CumulativeAlgebra S.R) (declared : DeclaredTypesFormed S.R)
  (choices : ExecutableChecking.HeadChoices S.R) (reducer : ExecutableReduction.Reducer S.R)

def solveBody (fuel : Nat) {Γ : Context S.R} (metavariableType : TypeOver Γ)
    {type : TypeOver (extend Γ metavariableType)} (spine : Spine type)
    (first second : Term spine.target spine.result) :
    ContextualDependentScopedDispatch.Result S.levels [spine.toScoped ⟨spine.result, first, second⟩] :=
  let closure := closed S.levels spine first second
  ⟨closure, ContextualDependentDispatch.step facts roots heads algebra declared choices reducer fuel metavariableType closure.equations⟩

end ContextualDependentPiSpineSolver
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
