import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentGeneralPatternRigidRefutation

/-!
# One certified solver step for general pattern equations

For a recognized pattern `F x̄` and a right side `t`, the step first inverts
`t` through the occurs-checked argument map and checks the candidate body
with the existing executable checker. Success returns the principal
definition update as an ordinary scoped solver result. Otherwise, when `t`
is certified normal, no outer metavariable of `t` is an elimination head,
and `t` uses a local that is not an argument, the step returns a refutation
valid in every future context. In every other case the scoped constraint is
retained unchanged:
budget exhaustion, conversion-hidden independence and non-pattern shapes
stay pending.

Every outcome has the same fixed-target reading, so a later worklist can
keep closed and symbolic solvability separate without inspecting how the
outcome was produced.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentGeneralPattern

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentPiSpine ContextualDependentTypedInversion
open ContextualDependentEta ContextualDependentScope

variable {Head L : Type} [UniverseLevel.LevelOrder L] {S : Setting Head L}

namespace Pattern

variable {Γ : Context S.R} {type : TypeOver Γ} {spine : Spine type}
  {scopeType : TypeOver (extend Γ type)} {scope : Spine scopeType}

/-- Certified outcomes of one step on `F x̄ ≐ right`. -/
inductive Outcome (pattern : Pattern spine scope)
    (right : Term scope.target ((lifted spine).result.reindex pattern.map.hom)) : Type
  | solved (result : ContextualDependentScopedDispatch.Result S.levels [pattern.constraint right])
      (finished : result.update.remaining = [])
  | refuted (absent : ∀ {Δ : Context S.R} (solution : Δ ⟶ extend Γ type),
      ¬ (pattern.constraint right).Holds solution)
  | pending

namespace Outcome

variable {pattern : Pattern spine scope}
  {right : Term scope.target ((lifted spine).result.reindex pattern.map.hom)}

/-- What remains to be solved at a fixed target context. -/
def Residual : Outcome pattern right → Context S.R → Prop
  | .solved result _, point => Nonempty (point ⟶ result.update.target)
  | .refuted _, _ => False
  | .pending, point => ∃ solution : point ⟶ extend Γ type, (pattern.constraint right).Holds solution

/-- Every outcome preserves exactly the solutions at each fixed target,
including the empty context. -/
theorem solutions_iff (outcome : Outcome pattern right) (point : Context S.R) :
    (∃ solution : point ⟶ extend Γ type, (pattern.constraint right).Holds solution) ↔
      outcome.Residual point := by
  cases outcome with
  | solved result finished =>
      have fixed := result.fixed_point_solutions_iff point
      rw [finished] at fixed
      change _ ↔ Nonempty (point ⟶ result.update.target)
      constructor
      · rintro ⟨solution, held⟩
        obtain ⟨residual, _⟩ := fixed.mp ⟨solution, fun constraint member => by
          obtain rfl := List.mem_singleton.mp member
          exact held⟩
        exact ⟨residual⟩
      · rintro ⟨residual⟩
        obtain ⟨solution, held⟩ := fixed.mpr ⟨residual, Frames.models_nil _⟩
        exact ⟨solution, held _ (List.mem_singleton_self _)⟩
  | refuted absent =>
      change _ ↔ False
      exact ⟨fun ⟨solution, held⟩ => absent solution held, False.elim⟩
  | pending => exact Iff.rfl

/-- A solved outcome is a principal answer for the original scoped equation. -/
theorem solved_principal (result : ContextualDependentScopedDispatch.Result S.levels [pattern.constraint right])
    (finished : result.update.remaining = []) :
    ContextualDependentScopedDispatch.Holds [pattern.constraint right] result.update.answer ∧
      ∀ (Δ : Context S.R) (solution : Δ ⟶ extend Γ type),
        ContextualDependentScopedDispatch.Holds [pattern.constraint right] solution →
          ∃ residual : Δ ⟶ result.update.target, ∀ term : TotalTerm (extend Γ type),
            (frames S.levels).E (term.reindex solution) (term.reindex (residual ≫ result.update.answer)) :=
  result.completed finished

end Outcome

section Witness

variable (pattern : Pattern spine scope)

/-- A support variable that is local and outside the argument image. -/
def outsideWitness (right : Tm Head scope.target.arity) : Option (Fin scope.target.arity) :=
  (List.finRange _).find? fun index =>
    decide (index ∈ right.support) && (scope.originEquiv.symm index).isRight &&
      (ContextualDependentInversion.lookup pattern.map.forward index).isNone

theorem outsideWitness_spec {right : Tm Head scope.target.arity} {index : Fin scope.target.arity}
    (found : pattern.outsideWitness right = some index) :
    index ∈ right.support ∧ ∃ outside : scope.Local, scope.localIndex outside = index ∧
      ∀ position, pattern.args position ≠ outside := by
  have selected := List.find?_some found
  simp only [Bool.and_eq_true, decide_eq_true_eq] at selected
  obtain ⟨⟨member, isLocal⟩, missing⟩ := selected
  refine ⟨member, ?_⟩
  cases origin : scope.originEquiv.symm index with
  | inl prior => rw [origin] at isLocal; cases isLocal
  | inr outside =>
      have located : scope.localIndex outside = index := by
        unfold Spine.localIndex
        rw [← origin, Equiv.apply_symm_apply]
      refine ⟨outside, located, fun position hit => ?_⟩
      have mapped : pattern.map.forward ((lifted spine).localIndex
          ((spine.localReindexEquiv (projectionHom Γ type)).symm position)) = index := by
        change argRen (lifted spine) scope idRen pattern.liftedArgs _ = index
        rw [argRen_local]
        change scope.localIndex (pattern.args ((spine.localReindexEquiv _)
          ((spine.localReindexEquiv _).symm position))) = index
        rw [Equiv.apply_symm_apply, hit, located]
      rw [← mapped, ContextualDependentInversion.lookup_complete _ pattern.map.injective] at missing
      cases missing

end Witness

section Step

variable [DecidableEq Head] [DecidableRel S.R.headEq]
  [∀ head, Decidable (S.R.isUniverse head)] [DecidableRel S.R.cumulative]
variable (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R)
  (heads : HeadPreserving S.R) (algebra : CumulativeAlgebra S.R) (declared : DeclaredTypesFormed S.R)
  (reflects : ContextualDependentReductionReflection.RootReflectsInjections S.R.computation)
  (complete : AlgorithmicComplete S.R S.roles)
  (rigid : ∀ name, S.roles name = .rigid)
  (normalizes : ∀ {Θ : Context S.R} {type : TypeOver Θ} (term : Term Θ type),
    ∃ code : Tm Head Θ.arity, ContextualDependentNormalChecking.Normal (S := S) code ∧
      Equal S.R Θ.raw term.code code type.code)
  (certifyNormal : ∀ {n : Nat} (term : Tm Head n),
    Option (PLift (ContextualDependentNormalChecking.Normal (S := S) term)))
  (choices : ExecutableChecking.HeadChoices S.R) (reducer : ExecutableReduction.Reducer S.R)

/-- The refutation branch, after inversion did not finish. -/
def tryRefute (pattern : Pattern spine scope)
    (right : Term scope.target ((lifted spine).result.reindex pattern.map.hom)) : Outcome pattern right :=
  match found : pattern.outsideWitness right.code with
  | none => .pending
  | some _ =>
      match certifyNormal right.code with
      | none => .pending
      | some normal =>
          if free : HeadFree (outerFlexible scope) right.code = true then
            .refuted fun solution => by
              obtain ⟨member, outside, located, notArgument⟩ := pattern.outsideWitness_spec found
              subst located
              exact pattern.refuted_rigid rigid complete normalizes right outside notArgument member
                free normal.down solution
          else .pending

/-- One general-pattern step. Inversion and checking supply the principal
answer; a certified out-of-image local supplies a refutation; otherwise the
scoped constraint stays pending. -/
def step (fuel : Nat) (pattern : Pattern spine scope)
    (right : Term scope.target ((lifted spine).result.reindex pattern.map.hom)) : Outcome pattern right :=
  match ContextualDependentTypedInversion.recover facts roots heads algebra declared choices reducer fuel
      pattern.bodyInclusion spine.result right.code with
  | some found => .solved (pattern.replace facts roots heads algebra reflects complete found.body right
      found.recovers.symm) rfl
  | none => tryRefute complete rigid normalizes certifyNormal pattern right

theorem step_of_recovered (fuel : Nat) (pattern : Pattern spine scope)
    (right : Term scope.target ((lifted spine).result.reindex pattern.map.hom))
    (found : Recovery pattern.bodyInclusion spine.result right.code)
    (computed : ContextualDependentTypedInversion.recover facts roots heads algebra declared choices reducer fuel
      pattern.bodyInclusion spine.result right.code = some found) :
    step facts roots heads algebra declared reflects complete rigid normalizes certifyNormal choices reducer
        fuel pattern right =
      .solved (pattern.replace facts roots heads algebra reflects complete found.body right found.recovers.symm) rfl := by
  unfold step
  rw [computed]

end Step

end Pattern
end ContextualDependentGeneralPattern
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
