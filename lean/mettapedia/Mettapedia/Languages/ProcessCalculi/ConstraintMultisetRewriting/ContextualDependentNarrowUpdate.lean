import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentUniverseNarrowing

/-!
# Narrowing the newest declaration, as an update of the store

Where every solution of a store sends its newest unknown, declared at a universe `V`, to a type equal to a type of
a smaller universe `U`, the store over the context that declares the unknown at `U` has exactly the solutions of
the store.

* `narrowHom`: the morphism from the narrowed context: the identity on codes, typed by cumulativity.
* **`narrowUpdate`**: the update whose target is the narrowed context and whose residual store is the store
  transported along `narrowHom`. It is sound by transport, and complete because the value of the unknown in a
  solution can be replaced by the type of `U` it is equal to: the two substitutions are equal as typed
  substitutions, by the injectivity of the inclusion of `U` in `V`.

The hypothesis `forced` is semantic; for the positions of `ContextualDependentUniverseInjective.HoldsVar` it is
`HoldsVar.small`.

**On the witness** (`narrow_principal`): `narrowStore`, `X ≐ Π (y : Y). Y` with `X : U0, Y : U1`, on which the top
family is stuck, **has a principal answer**: after `narrowUpdate` the top family commits on the residual store
(`narrow_remaining_committed`, evaluated by the kernel at budget 16), and the composite update is finished. So this
store, unlike `crossStore`, can be solved with a principal answer; what is missing is the rule that applies the
update.

The update keeps the weight rank and the permuted Miller class (`ContextualDependentNarrowUpdateRank`). Not done:
the executable reading that finds the update on an arbitrary store, and the family that applies it.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentEtaDepth

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentUpdate ContextualDependentWorklist
open ContextualDependentUniverseInjective

variable {Head L : Type} [UniverseLevel.LevelOrder L] {S : Setting Head L}

/-- The newest unknown of the narrowed context, as a term of the wide declaration. -/
def narrowedNewest (Γ : Context S.R) (wide small : TypeOver Γ) {u v : Head} (smallCode : small.code = .head u)
    (wideCode : wide.code = .head v) (lower : S.R.cumulative u v) :
    Term (extend Γ small) (wide.reindex (projectionHom Γ small)) where
  code := .var 0
  typed := by
    change Typed S.R (.snoc Γ.raw small.code) (.var 0) (subst (projectionHom Γ small).substitution wide.code)
    rw [wideCode, smallCode]
    exact Derivable.cumul (Derivable.var (R := S.R) (Γ := .snoc Γ.raw (.head u)) 0) lower

/-- **The morphism from the narrowed context**: the identity on codes. -/
def narrowHom (Γ : Context S.R) (wide small : TypeOver Γ) {u v : Head} (smallCode : small.code = .head u)
    (wideCode : wide.code = .head v) (lower : S.R.cumulative u v) : extend Γ small ⟶ extend Γ wide :=
  pair (projectionHom Γ small) (narrowedNewest Γ wide small smallCode wideCode lower)

section Update

variable (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R) (heads : HeadPreserving S.R)
  (algebra : CumulativeAlgebra S.R) (rigid : ∀ name, S.roles name = .rigid)
  (complete : AlgorithmicComplete S.R S.roles)

/-- **Narrowing the newest declaration**, as an update with exactly the store's solutions, where every solution
sends the newest unknown to a type equal to a type of the smaller universe. -/
def narrowUpdate (Γ : Context S.R) (wide small : TypeOver Γ) {u v : Head} (smallCode : small.code = .head u)
    (wideCode : wide.code = .head v) (lower : S.R.cumulative u v) (hv : S.R.isUniverse v)
    (problem : EquationStore (TotalTerm (extend Γ wide)))
    (forced : ∀ (Δ : Context S.R) (σ : Δ ⟶ extend Γ wide), (frames S.levels).Models σ problem →
      ∃ value, Typed S.R Δ.raw value (.head u) ∧ TypeEq S.R Δ.raw value (σ.substitution 0)) :
    Update S.levels problem where
  target := extend Γ small
  answer := narrowHom Γ wide small smallCode wideCode lower
  remaining := (frames S.levels).applyStore (narrowHom Γ wide small smallCode wideCode lower) problem
  sound := fun _ residual solved =>
    (Frames.models_applyStore (X := frames S.levels) (narrowHom Γ wide small smallCode wideCode lower) residual
      problem).mp solved
  complete := by
    intro Δ σ solved
    obtain ⟨value, tValue, eValue⟩ := forced Δ σ solved
    let restricted : Δ ⟶ Γ := σ ≫ projectionHom Γ wide
    let newest : Term Δ (small.reindex restricted) := ⟨value, by
      change Typed S.R Δ.raw value (subst restricted.substitution small.code)
      rw [smallCode]
      exact tValue⟩
    let residual : Δ ⟶ extend Γ small := pair restricted newest
    have same : homTypedEquality S.R σ (residual ≫ narrowHom Γ wide small smallCode wideCode lower) := by
      refine ⟨σ.typed, fun index => ?_⟩
      refine Fin.cases ?_ (fun index => ?_) index
      · have declared := σ.typed 0
        change Typed S.R Δ.raw (σ.substitution 0) (subst σ.substitution (Presentation.rename wk wide.code))
          at declared
        change Equal S.R Δ.raw (σ.substitution 0) value
          (subst σ.substitution (Presentation.rename wk wide.code))
        rw [wideCode] at declared ⊢
        obtain ⟨x, hx, equal⟩ := eValue
        exact .symm (universe_injective facts roots heads algebra rigid complete Δ.formed hv hx
          (Derivable.cumul tValue lower) declared equal)
      · exact .refl (σ.typed index.succ)
    exact ⟨residual,
      (Frames.models_applyStore (X := frames S.levels) (narrowHom Γ wide small smallCode wideCode lower) residual
        problem).mpr ((Elimination.models_pointwise S.levels (act_equal_of_substEq S.levels same) problem).mp solved),
      act_equal_of_substEq S.levels same⟩

end Update

end ContextualDependentEtaDepth

namespace ContextualDependentSweep.Witnesses

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentUpdate ContextualDependentWorklist ContextualDependentDynamicFragment
open ContextualDependentPatternFiring.Controls ContextualDependentAcceptance4
open ContextualDependentEtaDepth ContextualDependentEtaDepth.Controls ContextualDependentEtaDepth.ArgControls
open ContextualDependentEtaDepth.BaseControls

/-- **`narrowStore` with `Y` declared at `U0`**, as an update of `narrowStore`. -/
def narrowWitnessUpdate : Update setting.levels narrowStore :=
  narrowUpdate (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
    ContextualDependentPiSpine.Controls.rigid TowerModel.complete ctxAX largeType smallType
    (formIn_code _ _ _) (formIn_code _ _ _) (by decide +kernel) (by decide +kernel) narrowStore
    (fun _ σ solved => narrow_solutions_small σ solved)

/-- **The top family commits on the narrowed store**, at budget 16. -/
theorem narrow_remaining_committed :
    (run (sortTower.solver 16) narrowWitnessUpdate.remaining 2).readout = .commit := by decide +kernel

/-- **`narrowStore` has a principal answer.** -/
theorem narrow_principal :
    ∃ (Δ : Context setting.R) (answer : Δ ⟶ ctxAXY), (frames setting.levels).Principal narrowStore answer := by
  cases outcome : run (sortTower.solver 16) narrowWitnessUpdate.remaining 2 with
  | solved state finished => exact ⟨_, _, (narrowWitnessUpdate.then state).completed finished⟩
  | stuck _ =>
      have committed := narrow_remaining_committed
      rw [outcome] at committed
      cases committed
  | refuted _ =>
      have committed := narrow_remaining_committed
      rw [outcome] at committed
      cases committed
  | cutoff _ =>
      have committed := narrow_remaining_committed
      rw [outcome] at committed
      cases committed

/-- **A store of the fragment that has a principal answer and on which the top family is stuck** wherever its
compiled run reads `stuck`: the missing rule is the narrowing of a declaration. -/
theorem narrow_missing_rule_of_ending {fuel rounds : Nat}
    (read : endingSort fuel rounds ctxAXY narrowStore = .stuck) :
    InFragmentStore narrowStore ∧
      (∃ (Δ : Context setting.R) (answer : Δ ⟶ ctxAXY), (frames setting.levels).Principal narrowStore answer) ∧
      isStuck (run (sortTower.solver fuel) narrowStore rounds) = true :=
  ⟨narrow_in_fragment, narrow_principal, stuck_of_endingSort read⟩

end ContextualDependentSweep.Witnesses
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
