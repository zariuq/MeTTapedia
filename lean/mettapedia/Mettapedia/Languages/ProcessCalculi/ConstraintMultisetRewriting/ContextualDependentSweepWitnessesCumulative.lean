import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentSweepWitnessesSort

/-!
# Stuck stores where a local of a smaller universe is passed to an unknown declared at a larger one

Both stores are in the dynamic pattern fragment, and the top family (`sortTower`) is stuck on them wherever its
compiled run reads `stuck`; the kernel statements are in `ContextualDependentSweepWitnessesCumulativeRun`.

**`crossStore`**: over `X : U0 → U0, Y : U1 → U1`,

  `λ x. X x ≐ λ x. Y x`  at  `Π (x : U0). U1`.

It is solvable, in two ways that are proved here: `X := λ x. x, Y := λ z. z` (`cross_identity`) and
`X := λ x. G, Y := λ z. G` for the ground type `G` (`cross_constant`).

The store has no principal answer; that is proved in `ContextualDependentSweepWitnessesCumulativePrincipal`
(`cross_no_principal`). In outline: a solution is `Y := λ z. T` with `T` a type of `U1` over `z : U1` whose
instance at a variable `x : U0` is a type of `U0`. Both `T := z` and `T := G` are solutions. An answer that covers
both sends `Y` to `λ z. T₀` with `T₀` a neutral type that is not `z`; such a type keeps its universe when `z` is
read at `U1`, so it is a type of `U0` there, and no instance of it is `z` (a variable of `U1` is not a type of
`U0`). So the statement "a principal answer or a certified refutation" does not hold on this store.

**`fixedStore`**: over `F : U1 → U0`,

  `λ x. F x ≐ λ x. x`  at  `Π (x : U0). U0`.

It has no solution (`fixed_unsolvable`). The only candidate is `F := λ z. z`, and `z : U1` is not a type of `U0`.
The reason is the universe of a bound variable, which the refutation of a universe does not read. The statements
behind it are general: a variable declared at a universe is not equal to a type of a universe that does not lie
above it (`local_not_small`); an unknown declared at a larger universe, applied to a local of a smaller one, is not
equal to that local when its result universe does not hold the larger (`applied_local_apart`), because equality in
the context of the smaller local holds in the context of the larger (`equal_of_narrows`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentUniverseInjective

open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open TypedContextual.QuotientComprehensionSyntax
open ContextualDependentEtaLong ContextualDependentCumulative ContextualDependentRank

variable {Head L : Type} [UniverseLevel.LevelOrder L] {S : Setting Head L}
variable (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R) (heads : HeadPreserving S.R)
  (algebra : CumulativeAlgebra S.R) (rigid : ∀ name, S.roles name = .rigid)
  (complete : AlgorithmicComplete S.R S.roles)

include facts roots heads algebra rigid complete in
/-- **A variable declared at a universe is not equal to a type of a universe that does not lie above it.** -/
theorem local_not_small {n : Nat} {Γ : Ctx Head n} {v u : Head} (formed : CtxFormed S.R (.snoc Γ (.head v)))
    (hv : S.R.isUniverse v) (hu : S.R.isUniverse u) (apart : ¬ S.R.cumulative v u) {s : Tm Head (n + 1)}
    (ts : Typed S.R (.snoc Γ (.head v)) s (.head u)) : ¬ TypeEq S.R (.snoc Γ (.head v)) s (.var 0) := by
  intro equal
  have isV : IsType S.R (.snoc Γ (.head v)) (.head v) := IsType.head_of_universe hv
  have spine : Long S.R S.roles (.spine (.snoc Γ (.head v)) (.var 0) (.head v)) := .var 0 (IsType.refl isV)
  have normal : Long S.R S.roles (.type (.snoc Γ (.head v)) (.var 0)) :=
    .neutralType spine hv (IsType.refl isV).below
  have typed := normal_typed_of_equal facts roots heads algebra rigid complete formed hu ts equal normal
  have generation : TypeLe S.R (.snoc Γ (.head v)) (.head v) (.head u) := Typed.generation typed
  exact apart (typeLe_head_cumulative facts algebra formed hv hu generation)

include facts in
/-- **Two abstractions equal at a Π type have equal bodies**, by β at a fresh variable. -/
theorem equal_of_lam {n : Nat} {Γ : Ctx Head n} (formed : CtxFormed S.R Γ) {A : Tm Head n}
    {first second B : Tm Head (n + 1)} (equal : Equal S.R Γ (.lam first) (.lam second) (.pi A B)) :
    Equal S.R (.snoc Γ A) first second B := by
  obtain ⟨tFirst, tSecond⟩ := Equal.typed equal formed
  obtain ⟨w, hw, tPi⟩ := Typed.isType tFirst formed
  have bodyFirst : Typed S.R (.snoc Γ A) first B := Typed.lam_inv facts tFirst formed
  have bodySecond : Typed S.R (.snoc Γ A) second B := Typed.lam_inv facts tSecond formed
  have compared : Equal S.R (.snoc Γ A) (.app (Presentation.rename wk (.lam first)) (.var 0))
      (.app (Presentation.rename wk (.lam second)) (.var 0)) B := by
    have step := Derivable.appCong (equal.rename (CtxRen.wk Γ A))
      (Derivable.refl (Derivable.var (R := S.R) (Γ := .snoc Γ A) 0))
    simpa only [Presentation.rename, Ctx.lookup, Products.fresh_instantiation] using step
  have betaFirst : Equal S.R (.snoc Γ A) (.app (Presentation.rename wk (.lam first)) (.var 0)) first B := by
    have step := Derivable.betaPi (tPi.rename (CtxRen.wk Γ A)) hw
      (bodyFirst.rename ((CtxRen.wk Γ A).snoc A)) (Derivable.var (R := S.R) (Γ := .snoc Γ A) 0)
    simpa only [Presentation.rename, Ctx.lookup, Products.fresh_instantiation] using step
  have betaSecond : Equal S.R (.snoc Γ A) (.app (Presentation.rename wk (.lam second)) (.var 0)) second B := by
    have step := Derivable.betaPi (tPi.rename (CtxRen.wk Γ A)) hw
      (bodySecond.rename ((CtxRen.wk Γ A).snoc A)) (Derivable.var (R := S.R) (Γ := .snoc Γ A) 0)
    simpa only [Presentation.rename, Ctx.lookup, Products.fresh_instantiation] using step
  exact .trans (.symm betaFirst) (.trans compared betaSecond)

include facts roots heads algebra rigid complete in
/-- **An unknown declared at a larger universe, applied to a local of a smaller one, is not equal to that local**
when its result universe does not lie above the universe it is declared at: equality in the context of the smaller
local holds in the context of the larger (narrowing reflects equality), where the local is not a type of the result
universe. -/
theorem applied_local_apart {n : Nat} {Γ : Ctx Head n} (formed : CtxFormed S.R Γ) {v w u : Head}
    (hv : S.R.isUniverse v) (hw : S.R.isUniverse w) (hu : S.R.isUniverse u)
    (lower : S.R.cumulative w v) (below : S.R.cumulative u v) (apart : ¬ S.R.cumulative v u)
    {f : Tm Head n} (tf : Typed S.R Γ f (.pi (.head v) (.head u))) :
    ¬ TypeEq S.R (.snoc Γ (.head w)) (.app (Presentation.rename wk f) (.var 0)) (.var 0) := by
  rintro ⟨x, hx, equal⟩
  have formedWide : CtxFormed S.R (.snoc Γ (.head v)) := formed.snoc (IsType.head_of_universe hv)
  have formedNarrow : CtxFormed S.R (.snoc Γ (.head w)) := formed.snoc (IsType.head_of_universe hw)
  have narrows : CtxNarrows S.R (.snoc Γ (.head v)) (.snoc Γ (.head w)) := .lower (CtxNarrows.refl Γ) lower
  have applied : Typed S.R (.snoc Γ (.head v)) (.app (Presentation.rename wk f) (.var 0)) (.head u) :=
    Derivable.appElim (tf.rename (CtxRen.wk Γ (.head v))) (Derivable.var (R := S.R) (Γ := .snoc Γ (.head v)) 0)
  have appliedWide : Typed S.R (.snoc Γ (.head v)) (.app (Presentation.rename wk f) (.var 0)) (.head v) :=
    Derivable.cumul applied below
  have varWide : Typed S.R (.snoc Γ (.head v)) (.var 0) (.head v) :=
    Derivable.var (R := S.R) (Γ := .snoc Γ (.head v)) 0
  have narrowEq : Equal S.R (.snoc Γ (.head w)) (.app (Presentation.rename wk f) (.var 0)) (.var 0) (.head v) :=
    universe_injective facts roots heads algebra rigid complete formedNarrow hv hx
      (typed_narrow narrows appliedWide) (typed_narrow narrows varWide) equal
  have wideEq := equal_of_narrows facts roots heads algebra rigid complete narrows formedWide formedNarrow
    appliedWide varWide narrowEq
  exact local_not_small facts roots heads algebra rigid complete formedWide hv hu apart applied ⟨v, hv, wideEq⟩

end ContextualDependentUniverseInjective

namespace ContextualDependentSweep.Witnesses

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentWorklist ContextualDependentDynamicFragment
open ContextualDependentPatternFiring.Controls ContextualDependentAcceptance4
open ContextualDependentEtaDepth ContextualDependentEtaDepth.Controls ContextualDependentEtaDepth.ArgControls
open ContextualDependentEtaDepth.BaseControls

/-! ## An unknown of the smaller universe against an unknown of the larger, at a local of the smaller -/

/-- `U0 → U0`, over no unknown. -/
def smallFamily : TypeOver (empty setting.R) :=
  formIn (empty setting.R) (.pi (.head (.sort Tower.zero)) (.head (.sort Tower.zero))) (by decide +kernel)

/-- `X : U0 → U0`. -/
abbrev ctxSmall := extend (empty setting.R) smallFamily

/-- `U1 → U1`, over `X`. -/
def largeFamily : TypeOver ctxSmall :=
  formIn ctxSmall (.pi (.head (.sort (.succ Tower.zero))) (.head (.sort (.succ Tower.zero)))) (by decide +kernel)

/-- `X : U0 → U0, Y : U1 → U1`. -/
abbrev ctxCross := extend ctxSmall largeFamily

/-- `Π (x : U0). U1`, over `X Y`. -/
def crossType : TypeOver ctxCross :=
  formIn ctxCross (.pi (.head (.sort Tower.zero)) (.head (.sort (.succ Tower.zero)))) (by decide +kernel)

/-- `λ x. X x ≐ λ x. Y x` at `Π (x : U0). U1`. -/
def crossEquation : Equation (TotalTerm ctxCross) :=
  (termIn ctxCross crossType (.lam (.app (.var 2) (.var 0))) (by decide +kernel),
    termIn ctxCross crossType (.lam (.app (.var 1) (.var 0))) (by decide +kernel))
def crossStore : EquationStore (TotalTerm ctxCross) := [crossEquation]

/-- The raw problem of the sweep. -/
def crossProblem : Problem :=
  { unknowns := [.pi .u0 .u0, .pi .u1 .u1],
    equations := [(.pi .u0 .u1, .lam (.app (.var 2) (.var 0)), .lam (.app (.var 1) (.var 0)))] }

theorem cross_in_fragment : InFragmentStore crossStore := storeInside_sound (by decide +kernel)

/-- `X := λ x. x, Y := λ z. z`. -/
def crossIdentity : empty setting.R ⟶ ctxCross :=
  Elimination.instantiate (empty setting.R) (termIn (empty setting.R) smallFamily (.lam (.var 0)) (by decide +kernel)).2 ≫
    Elimination.instantiate ctxSmall (termIn ctxSmall largeFamily (.lam (.var 0)) (by decide +kernel)).2

/-- `X := λ x. G, Y := λ z. G`, for the ground type `G`. -/
def crossConstant : empty setting.R ⟶ ctxCross :=
  Elimination.instantiate (empty setting.R)
      (termIn (empty setting.R) smallFamily (.lam (.head .legacyGround)) (by decide +kernel)).2 ≫
    Elimination.instantiate ctxSmall (termIn ctxSmall largeFamily (.lam (.head .legacyGround)) (by decide +kernel)).2

/-- **The store is solvable** by the identities. -/
theorem cross_identity : (frames setting.levels).Solvable crossStore :=
  solvable_by crossIdentity crossEquation.1.2 crossEquation.2.2 (by decide +kernel)

/-- **The store is solvable** by the constant families at the ground type. -/
theorem cross_constant : (frames setting.levels).Solvable crossStore :=
  solvable_by crossConstant crossEquation.1.2 crossEquation.2.2 (by decide +kernel)

/-- **A store of the fragment, solvable, on which the top family is stuck** wherever its compiled run reads
`stuck`. -/
theorem cross_gap_of_ending {fuel rounds : Nat} (read : endingSort fuel rounds ctxCross crossStore = .stuck) :
    InFragmentStore crossStore ∧ (frames setting.levels).Solvable crossStore ∧
      isStuck (run (sortTower.solver fuel) crossStore rounds) = true :=
  ⟨cross_in_fragment, cross_identity, stuck_of_endingSort read⟩

/-! ## An unknown declared at the larger universe against the local itself -/

/-- `U1 → U0`, over no unknown. -/
def mixedFamily : TypeOver (empty setting.R) :=
  formIn (empty setting.R) (.pi (.head (.sort (.succ Tower.zero))) (.head (.sort Tower.zero))) (by decide +kernel)

/-- `F : U1 → U0`. -/
abbrev ctxMixed := extend (empty setting.R) mixedFamily

/-- `Π (x : U0). U0`, over `F`. -/
def fixedType : TypeOver ctxMixed :=
  formIn ctxMixed (.pi (.head (.sort Tower.zero)) (.head (.sort Tower.zero))) (by decide +kernel)

/-- `λ x. F x ≐ λ x. x` at `Π (x : U0). U0`. -/
def fixedEquation : Equation (TotalTerm ctxMixed) :=
  (termIn ctxMixed fixedType (.lam (.app (.var 1) (.var 0))) (by decide +kernel),
    termIn ctxMixed fixedType (.lam (.var 0)) (by decide +kernel))
def fixedStore : EquationStore (TotalTerm ctxMixed) := [fixedEquation]

/-- The raw problem of the sweep. -/
def fixedProblem : Problem :=
  { unknowns := [.pi .u1 .u0], equations := [(.pi .u0 .u0, .lam (.app (.var 1) (.var 0)), .lam (.var 0))] }

theorem fixed_in_fragment : InFragmentStore fixedStore := storeInside_sound (by decide +kernel)

/-- **The store has no solution**: under a solution `F := f`, the bodies `f x` and `x` are equal for `x : U0`, and
an unknown declared at `U1 → U0` applied to a local of `U0` is never equal to that local. -/
theorem fixed_unsolvable : ¬ (frames setting.levels).Solvable fixedStore := by
  rintro ⟨Δ, σ, solved⟩
  have held := solved fixedEquation List.mem_cons_self
  rw [ContextualDependentRigidFormers.solves_raw] at held
  obtain ⟨_, equal⟩ := held
  have typeCode : fixedEquation.1.1.code = .pi (.head (.sort Tower.zero)) (.head (.sort Tower.zero)) :=
    formIn_code _ _ _
  rw [typeCode] at equal
  have bodies := ContextualDependentUniverseInjective.equal_of_lam (S := setting) TowerModel.facts Δ.formed equal
  have familyCode : mixedFamily.code = .pi (.head (.sort (.succ Tower.zero))) (.head (.sort Tower.zero)) :=
    formIn_code _ _ _
  have declared := σ.typed (⟨0, Nat.zero_lt_one⟩ : Fin 1)
  change Typed setting.R Δ.raw (σ.substitution (⟨0, Nat.zero_lt_one⟩ : Fin 1))
    (subst σ.substitution (Presentation.rename wk mixedFamily.code)) at declared
  rw [familyCode] at declared
  exact ContextualDependentUniverseInjective.applied_local_apart (S := setting) TowerModel.facts TowerModel.roots
    TowerModel.heads TowerModel.algebra ContextualDependentPiSpine.Controls.rigid TowerModel.complete Δ.formed
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) declared ⟨_, by decide +kernel, bodies⟩

/-- The top family is stuck on the store wherever its compiled run reads `stuck`. -/
theorem fixed_stuck_of_ending {fuel rounds : Nat} (read : endingSort fuel rounds ctxMixed fixedStore = .stuck) :
    InFragmentStore fixedStore ∧ isStuck (run (sortTower.solver fuel) fixedStore rounds) = true :=
  ⟨fixed_in_fragment, stuck_of_endingSort read⟩

end ContextualDependentSweep.Witnesses
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
