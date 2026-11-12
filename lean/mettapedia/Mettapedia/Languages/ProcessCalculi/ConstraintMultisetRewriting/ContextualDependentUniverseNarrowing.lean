import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentSweepWitnessesSort

/-!
# Every solution lowers the unknown: the semantic half of narrowing a declaration

Where an equation compares a type of a universe `U` with a type that holds an unknown `Y` of a larger universe, the
equation is not refuted and cannot be solved as it stands: its solutions are exactly those that send `Y` to a type of
`U`. This module proves the half of that statement that a rule needs for completeness.

* `HoldsVar y t`: `t` holds the variable `y` at a type position reached through the domains of Π types, the first
  components of Σ types and the types of identity types.
* **`HoldsVar.small`**: if a type of `U` is equal to an instance of such a `t`, the instance of `y` is equal to a
  type of `U`. By `small_pi`, `small_sigma`, `small_id`.
* On the witness (`narrow_solutions_small`): in every solution of `narrowStore`, `X ≐ Π (y : Y). Y` with
  `X : U0, Y : U1`, the value of `Y` is equal to a type of `U0`. So the answer that declares `Y` at `U0` loses no
  solution.

Not done here: the rule. It replaces the declaration of `Y` by the smaller universe (the identity substitution is
a typed substitution into the narrowed context, `CtxNarrows.substMor`), and reads the store there; this keeps both
components of the rank. Positions under a binder (the codomain of a Π type) need the same statement with the
instance of `y` weakened, hence a strengthening of typing.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentUniverseInjective

open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEtaLong ContextualDependentCumulative ContextualDependentRank

variable {Head L : Type} [UniverseLevel.LevelOrder L] {S : Setting Head L}

/-- **`t` holds the variable `y` at a type position** reached through domains, first components and the types of
identity types. -/
inductive HoldsVar {n : Nat} (y : Fin n) : Tm Head n → Prop where
  | here : HoldsVar y (.var y)
  | piDomain {A : Tm Head n} {B : Tm Head (n + 1)} : HoldsVar y A → HoldsVar y (.pi A B)
  | sigmaFirst {A : Tm Head n} {B : Tm Head (n + 1)} : HoldsVar y A → HoldsVar y (.sigma A B)
  | id {A a b : Tm Head n} : HoldsVar y A → HoldsVar y (.id A a b)

variable (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R) (heads : HeadPreserving S.R)
  (algebra : CumulativeAlgebra S.R) (rigid : ∀ name, S.roles name = .rigid)
  (complete : AlgorithmicComplete S.R S.roles)

include facts roots heads algebra rigid complete in
/-- **If a type of a universe is equal to an instance of a type that holds `y`, the instance of `y` is equal to a
type of that universe.** -/
theorem HoldsVar.small {n : Nat} {y : Fin n} {t : Tm Head n} (holds : HoldsVar (Head := Head) y t) :
    ∀ {m : Nat} {Δ : Ctx Head m}, CtxFormed S.R Δ → ∀ {u : Head}, S.R.isUniverse u → ∀ (σ : Sub Head n m)
      {s : Tm Head m}, Typed S.R Δ s (.head u) → TypeEq S.R Δ s (Presentation.subst σ t) →
        ∃ small, Typed S.R Δ small (.head u) ∧ TypeEq S.R Δ small (σ y) := by
  induction holds with
  | here => intro m Δ _ u _ σ s ts equal; exact ⟨s, ts, equal⟩
  | piDomain _ ih =>
      intro m Δ formed u hu σ s ts equal
      obtain ⟨_, _, tA, eA, _, _⟩ := small_pi facts roots heads algebra rigid complete formed hu ts equal
      exact ih formed hu σ tA eA
  | sigmaFirst _ ih =>
      intro m Δ formed u hu σ s ts equal
      obtain ⟨_, _, tA, eA, _, _⟩ := small_sigma facts roots heads algebra rigid complete formed hu ts equal
      exact ih formed hu σ tA eA
  | id _ ih =>
      intro m Δ formed u hu σ s ts equal
      obtain ⟨_, tA, eA⟩ := small_id facts roots heads algebra rigid complete formed hu ts equal
      exact ih formed hu σ tA eA

end ContextualDependentUniverseInjective

namespace ContextualDependentSweep.Witnesses

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentWorklist ContextualDependentDynamicFragment
open ContextualDependentPatternFiring.Controls ContextualDependentAcceptance4
open ContextualDependentEtaDepth ContextualDependentEtaDepth.Controls ContextualDependentEtaDepth.ArgControls
open ContextualDependentEtaDepth.BaseControls ContextualDependentUniverseInjective

/-- **In every solution of `X ≐ Π (y : Y). Y`, the value of `Y` is equal to a type of `U0`.** -/
theorem narrow_solutions_small {Δ : Context setting.R} (σ : Δ ⟶ ctxAXY)
    (solved : (frames setting.levels).Models σ narrowStore) :
    ∃ small, Typed setting.R Δ.raw small (.head (.sort Tower.zero)) ∧
      TypeEq setting.R Δ.raw small (σ.substitution (⟨0, Nat.zero_lt_succ 2⟩ : Fin 3)) := by
  have held := solved narrowEquation List.mem_cons_self
  obtain ⟨_, equal⟩ := (ContextualDependentRigidFormers.solves_raw (S := setting) σ narrowEquation).mp held
  have typeCode : narrowEquation.1.1.code = .head (.sort (.succ Tower.zero)) := formIn_code _ _ _
  rw [typeCode] at equal
  have smallCode : universeA.code = .head (.sort Tower.zero) := formIn_code _ _ _
  have tX := σ.typed (⟨1, Nat.succ_lt_succ (Nat.zero_lt_succ 1)⟩ : Fin 3)
  change Typed setting.R Δ.raw (σ.substitution (⟨1, Nat.succ_lt_succ (Nat.zero_lt_succ 1)⟩ : Fin 3))
    (subst σ.substitution (Presentation.rename wk (Presentation.rename wk universeA.code))) at tX
  rw [smallCode] at tX
  exact HoldsVar.small (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
    ContextualDependentPiSpine.Controls.rigid TowerModel.complete (.piDomain .here) Δ.formed (by decide +kernel)
    σ.substitution tX ⟨_, by decide +kernel, equal⟩

end ContextualDependentSweep.Witnesses
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
